import express from 'express';
import { randomUUID } from 'crypto';
import { chatAgent, getAgentSessionKey, sanitizeContextTags } from '../agent.js';
import { getGateway } from '../gateway.js';
import { hasDriveAuth, getDriveClient, getOrCreateBackupFolder, getDriveConfig } from './drive.js';
import { notify } from './notifications.js';
import { Readable } from 'stream';
import fs from 'fs';
import path from 'path';
import { safeWriteFileSync, BASE_PATH } from '../utils.js';
import { withMutex } from '../file-lock.js';
import { recordAudit } from './audit.js';
import { createLogger } from '../logger.js';
import { safeBroadcast } from '../broadcast.js';

const log = createLogger('Meetings');

const router = express.Router();

// Active meetings store
const meetings = new Map();

// Constants
const MAX_ACTIVE_MEETINGS = 50;
const MAX_MESSAGES_PER_MEETING = 200;  // H7 Fix: Cap at 200 messages

// Meeting ID format: mtg_ + 12 hex chars
const VALID_MEETING_ID = /^mtg_[a-f0-9]{12}$/;
const DEPT_RESPONSE_TIMEOUT = 180000; // 180s — 球赛分析需要较长推理时间，60s 不够
const NEGOTIATION_TIMEOUT = 600000; // 10 minutes

// Fix A: 超时后继续认领迟到回复（agent run 在 OpenClaw 侧会跑完，回复不能被丢弃）
const LATE_REPLY_POLL_INTERVAL_MS = 30000;
const LATE_REPLY_MAX_WAIT_MS = 600000; // 最长认领 10 分钟
// Fix B: 会议轮次 mutex 必须活得比一整轮更久（agents × DEPT_RESPONSE_TIMEOUT + 余量），
// 否则排队中的消息会在锁等待期间被静默丢弃
const MEETING_ROUND_MUTEX_TIMEOUT_MS = 1200000; // 20 minutes

// ---- Fix A: 迟到回复认领 ----
// lateReplyClaimed: `${meetingId}:${agentId}:${epoch}` — 防止同一轮重复回填
// lateReplyTimersMap: meetingId -> Map<agentId, timer>（纯运行时结构，不参与 JSON 序列化）
// activeClaims: `${meetingId}:${agentId}` -> epoch，用于戳掉旧 timer 的在途回调（防串台）
const lateReplyClaimed = new Set();
const lateReplyTimersMap = new Map();
const activeClaims = new Map();
let claimEpochCounter = 0;

async function backfillLateReply(meeting, agentId, wss, rawText, roundId, key) {
  // Fix 2: 会议已结束则放弃回填 — 防止向已结束会议追加消息/写盘/广播
  if (meeting.status === 'ended' || lateReplyClaimed.has(key) || !rawText) return;
  lateReplyClaimed.add(key);

  const { reasoning, conclusion } = parseAgentReply(rawText);
  const reply = `【迟到回复·超时后补记】${rawText}`;
  meeting.messages.push({
    role: 'agent',
    agentId,
    text: reply,
    reasoning,
    conclusion,
    late: true,
    timestamp: Date.now(),
  });
  if (meeting.messages.length > MAX_MESSAGES_PER_MEETING) {
    const first10 = meeting.messages.slice(0, 10);
    const lastN = meeting.messages.slice(-(MAX_MESSAGES_PER_MEETING - 10));
    meeting.messages = [...first10, ...lastN];
  }
  try { await persistMeeting(meeting); } catch { /* ignore */ }
  log.info(`Late reply from ${agentId} backfilled into ${meeting.id}`);
  if (wss) {
    safeBroadcast(wss, {
      event: 'meeting:agent-response',
      data: {
        meetingId: meeting.id,
        agentId,
        text: reply,
        reasoning,
        conclusion,
        roundId: roundId || null,
        late: true,
        timestamp: Date.now(),
      },
    });
  }
}

function clearLateReplyTimers(meeting) {
  const timers = lateReplyTimersMap.get(meeting.id);
  if (timers) {
    for (const t of timers.values()) clearInterval(t);
    lateReplyTimersMap.delete(meeting.id);
  }
  // Fix: 同步清除该会议所有 epoch 的认领标记，防止旧 key 残留导致跨轮串台
  // meetingId 固定长度（mtg_+12hex），前缀匹配 = 精确匹配
  const prefix = `${meeting.id}:`;
  for (const key of lateReplyClaimed) {
    if (key.startsWith(prefix)) lateReplyClaimed.delete(key);
  }
  for (const claimKey of activeClaims.keys()) {
    if (claimKey.startsWith(prefix)) activeClaims.delete(claimKey);
  }
}

function claimLateReply(meeting, agentId, sessionKey, agentPromise, sentAt, wss, roundId) {
  // Fix 1(rev): epoch 每轮自增 — key 自带 epoch、绝不跨轮复用；
  // 同时戳掉旧 timer（含在途回调），根治"第二轮起迟到回复被静默丢弃 / 旧回复串入新轮"
  if (meeting.status === 'ended') return;
  const claimKey = `${meeting.id}:${agentId}`;
  claimEpochCounter += 1;
  const epoch = claimEpochCounter;
  activeClaims.set(claimKey, epoch);
  const key = `${claimKey}:${epoch}`;
  lateReplyClaimed.delete(key);

  const isCurrent = () => activeClaims.get(claimKey) === epoch;

  // 清掉该会议+agent 上一轮残留的 timer（模块级 Map）
  const timers = lateReplyTimersMap.get(meeting.id);
  const oldTimer = timers ? timers.get(agentId) : null;
  if (oldTimer) clearInterval(oldTimer);

  // 路径 1：WS 未断时，被放弃的 chatAgent promise 仍可能正常 resolve
  if (agentPromise && typeof agentPromise.then === 'function') {
    agentPromise
      .then((r) => {
        if (isCurrent() && r && r.success && r.reply) backfillLateReply(meeting, agentId, wss, r.reply, roundId, key);
      })
      .catch(() => {});
  }

  // 路径 2：轮询会话历史 — 覆盖 WS 断连重连（pendingRequests 被清空、promise 永不 settle）的情况
  const deadline = Date.now() + LATE_REPLY_MAX_WAIT_MS;
  const timer = setInterval(async () => {
    try {
      if (!isCurrent() || Date.now() > deadline || meeting.status === 'ended' || lateReplyClaimed.has(key)) {
        clearInterval(timer);
        const ts = lateReplyTimersMap.get(meeting.id);
        if (ts) ts.delete(agentId);
        return;
      }
      const gw = getGateway();
      if (!gw.isReady) return;
      const msgs = await gw.getChatHistory(sessionKey, 6);
      for (let i = (msgs || []).length - 1; i >= 0; i--) {
        const m = msgs[i];
        if (m.role !== 'assistant') continue;
        let text = '';
        if (typeof m.content === 'string') text = m.content;
        else if (Array.isArray(m.content)) {
          text = m.content.filter(c => c.type === 'text' && c.text).map(c => c.text).join('\n');
        }
        const ts = typeof m.timestamp === 'number' ? m.timestamp : (Date.parse(m.timestamp || '') || 0);
        if (!text || ts < sentAt - 30000) continue;
        clearInterval(timer);
        const mts = lateReplyTimersMap.get(meeting.id);
        if (mts) mts.delete(agentId);
        backfillLateReply(meeting, agentId, wss, text, roundId, key);
        return;
      }
    } catch { /* gateway 忙/断连 — 下一轮重试 */ }
  }, LATE_REPLY_POLL_INTERVAL_MS);

  if (!timers) {
    lateReplyTimersMap.set(meeting.id, new Map([[agentId, timer]]));
  } else {
    timers.set(agentId, timer);
  }
}

// Ensure meetings directory exists
const MEETINGS_DIR = path.join(BASE_PATH, 'departments', 'meetings');
if (!fs.existsSync(MEETINGS_DIR)) {
  fs.mkdirSync(MEETINGS_DIR, { recursive: true });
}

/**
 * Parse agent reply into { reasoning, conclusion }.
 * Splits on the 【结论】 marker: everything before is reasoning,
 * everything after is conclusion. If the marker is missing,
 * returns { reasoning: '', conclusion: '' } so callers can
 * fall back to displaying the full reply text.
 */
function parseAgentReply(reply) {
  if (typeof reply !== 'string') {
    return { reasoning: '', conclusion: '' };
  }
  const idx = reply.indexOf('【结论】');
  if (idx === -1) {
    return { reasoning: '', conclusion: '' };
  }
  const reasoning = reply
    .slice(0, idx)
    .replace(/^【思考过程】/, '')
    .trim();
  const conclusion = reply.slice(idx + '【结论】'.length).trim();
  return { reasoning, conclusion };
}

// Load meetings from disk on startup (async with parallel file reads)
async function loadMeetingsFromDisk() {
  const dir = path.join(BASE_PATH, 'departments', 'meetings');
  if (!fs.existsSync(dir)) {
    fs.mkdirSync(dir, { recursive: true });
    return;
  }

  try {
    const files = await fs.promises.readdir(dir);
    const jsonFiles = files.filter(f => f.endsWith('.json'));

    // Read all files in parallel for faster startup
    const fileReads = jsonFiles.map(async (file) => {
      try {
        const content = await fs.promises.readFile(path.join(dir, file), 'utf8');
        const data = JSON.parse(content);
        if (data.id && (data.status === 'active' || data.status === 'ended')) {
          return data;
        }
      } catch (err) {
        log.warn(`Failed to parse ${file}: ${err.message}`);
      }
      return null;
    });

    const results = await Promise.all(fileReads);

    // Add valid meetings to map
    for (const data of results) {
      if (data) {
        meetings.set(data.id, data);
      }
    }

    log.info(`Loaded ${meetings.size} active meetings from disk`);
  } catch (err) {
    log.error(`Failed to load meetings: ${err.message}`);
  }
}
// Start loading async (don't block server startup)
loadMeetingsFromDisk().catch(err => log.error(`Meeting load error: ${err.message}`));

// Clean up old meeting files (older than 30 days) - async version with parallel I/O
async function cleanupOldMeetings() {
  try {
    const dir = path.join(BASE_PATH, 'departments', 'meetings');
    if (!fs.existsSync(dir)) return;
    const now = Date.now();
    const MAX_AGE_MS = 30 * 24 * 60 * 60 * 1000; // 30 days

    const files = await fs.promises.readdir(dir);
    const jsonFiles = files.filter(f => f.endsWith('.json'));

    // Check files in parallel, collect files to delete
    const checks = jsonFiles.map(async (file) => {
      try {
        const filePath = path.join(dir, file);
        const stat = await fs.promises.stat(filePath);
        if (now - stat.mtimeMs > MAX_AGE_MS) {
          return filePath;
        }
      } catch {}
      return null;
    });

    const filesToDelete = (await Promise.all(checks)).filter(Boolean);

    // Delete files in parallel
    if (filesToDelete.length > 0) {
      await Promise.all(filesToDelete.map(fp => fs.promises.unlink(fp).catch(() => {})));
      log.info(`Cleaned up ${filesToDelete.length} old meeting files`);
    }
  } catch (err) {
    log.warn('Cleanup error:', err.message);
  }
}

// Run cleanup on startup and every 6 hours
cleanupOldMeetings().catch(err => log.warn('Initial cleanup error:', err.message));
setInterval(() => {
  cleanupOldMeetings().catch(err => log.warn('Periodic cleanup error:', err.message));
}, 6 * 60 * 60 * 1000);

// Persist meeting to disk (async to avoid blocking event loop)
async function persistMeeting(meeting) {
  const dir = path.join(BASE_PATH, 'departments', 'meetings');
  if (!fs.existsSync(dir)) fs.mkdirSync(dir, { recursive: true });
  const filePath = path.join(dir, `${meeting.id}.json`);
  const data = JSON.stringify(meeting, null, 2);

  // Use async write to avoid blocking event loop
  try {
    await fs.promises.writeFile(filePath + '.tmp', data, 'utf8');
    await fs.promises.rename(filePath + '.tmp', filePath);
  } catch (err) {
    log.error(`Failed to persist meeting ${meeting.id}: ${err.message}`);
    // Fallback to sync for critical data safety
    safeWriteFileSync(filePath, data);
  }
}

/**
 * POST /api/meetings
 * Create a new meeting with selected departments
 * Body: { topic: string, agentIds: string[], initiatorAgentId: string }
 */
router.post('/', async (req, res) => {
  const { topic, agentIds, initiatorAgentId } = req.body;
  if (!topic || typeof topic !== 'string' || !Array.isArray(agentIds) || agentIds.length < 2) {
    return res.status(400).json({ error: 'topic and at least 2 agentIds required' });
  }
  if (topic.length > 500) {
    return res.status(400).json({ error: 'topic must be 500 characters or less' });
  }
  if (agentIds.length > 20 || !agentIds.every(id => typeof id === 'string' && id.length <= 50)) {
    return res.status(400).json({ error: 'invalid agentIds' });
  }

  // Fix C: gateway 未就绪时拒绝建会，避免产生所有发送必然失败的"死会议"
  const gwForCreate = getGateway();
  if (!gwForCreate.isReady) {
    try { await gwForCreate.waitForReady(10000); } catch { /* 保持未就绪则拒绝 */ }
  }
  if (!gwForCreate.isReady) {
    log.warn('Meeting creation rejected: OpenClaw gateway not connected');
    return res.status(503).json({ error: 'OpenClaw gateway 未连接，无法创建会议（请确认 OpenClaw 已启动后再试）' });
  }

  // Use mutex to prevent TOCTOU race condition on meeting creation
  const result = await withMutex('meeting-creation', async () => {
    // Auto-end all existing active meetings before creating a new one (only 1 active at a time)
    const activeMeetings = [...meetings.values()].filter(m => m.status === 'active');
    for (const oldMtg of activeMeetings) {
      oldMtg._cancelRequested = true;
      clearLateReplyTimers(oldMtg);
      oldMtg.status = 'ended';
      oldMtg.endedAt = Date.now();
      await persistMeeting(oldMtg);
      log.info(`Auto-ended ${oldMtg.id} (new meeting starting)`);
      recordAudit({ action: 'meeting:auto-end', target: oldMtg.id, details: { reason: 'superseded' }, ip: req.ip });
    }

    const meetingId = 'mtg_' + randomUUID().replace(/-/g, '').substring(0, 12);
    const meeting = {
      id: meetingId,
      topic,
      agentIds,
      initiatorAgentId: initiatorAgentId || agentIds[0],
      messages: [],
      status: 'active',
      createdAt: Date.now(),
    };
    meetings.set(meetingId, meeting);
    await persistMeeting(meeting);

    log.info(`Created ${meetingId}: ${topic} with ${agentIds.join(', ')}`);
    recordAudit({ action: 'meeting:create', target: meetingId, details: { topic, agentIds }, ip: req.ip });

    return { error: false, meeting, meetingId };
  });

  if (result.error) {
    return res.status(result.status).json(result.data);
  }

  const { meeting, meetingId } = result;

  // Broadcast meeting:start event to WebSocket clients
  try {
    const wss = req.app.locals.wss;
    if (wss) {
      const stats = safeBroadcast(wss, {
        event: 'meeting:start',
        data: {
          meetingId: meeting.id,
          topic: meeting.topic,
          agentIds: meeting.agentIds
        },
        timestamp: new Date().toISOString()
      });
      log.info(`Broadcast meeting:start to ${stats.sent} WS clients (total: ${wss.clients.size})`);
    } else {
      log.info('No wss available for broadcast');
    }
  } catch (err) {
    log.error(`WS broadcast error: ${err.message}`);
  }

  res.json({ success: true, meetingId, meeting });
});

/**
 * GET /api/meetings
 * List active meetings
 */
router.get('/', (req, res) => {
  // BUG2 fix: list BOTH active and ended meetings (newest first) so
  // historical meeting records stay visible in the UI.
  const list = [...meetings.values()]
    .sort((a, b) => b.createdAt - a.createdAt)
    .map(m => ({
      id: m.id,
      topic: m.topic,
      agentIds: m.agentIds,
      messageCount: m.messages.length,
      status: m.status,
      createdAt: m.createdAt,
      endedAt: m.endedAt || null
    }));
  res.json({ meetings: list });
});

/**
 * GET /api/meetings/:id
 * Get meeting details with message history
 */
router.get('/:id', (req, res) => {
  if (!VALID_MEETING_ID.test(req.params.id)) {
    return res.status(400).json({ error: 'Invalid meeting ID format' });
  }
  const meeting = meetings.get(req.params.id);
  if (!meeting) return res.status(404).json({ error: 'Meeting not found' });
  res.json({ success: true, meeting });
});

/**
 * POST /api/meetings/:id/message
 * Send a message to the meeting — broadcasts to ALL members, or a chosen subset
 * Body: { message: string, fromAgentId?: string, targetAgentIds?: string[] }
 *
 * If targetAgentIds is provided, ONLY those members receive and answer the message
 * (others stay in the meeting but are not disturbed).
 *
 * If fromAgentId is provided, the message is sent as context to all OTHER agents.
 * Each department gets the meeting context + conversation history and generates a response.
 * This creates REAL cross-department interaction.
 *
 * Returns immediately with a roundId, then streams department responses via WebSocket.
 */
router.post('/:id/message', async (req, res) => {
  if (!VALID_MEETING_ID.test(req.params.id)) {
    return res.status(400).json({ error: 'Invalid meeting ID format' });
  }
  const meeting = meetings.get(req.params.id);
  if (!meeting) return res.status(404).json({ error: 'Meeting not found' });

  // P0 Fix #6: Reject messages to ended meetings
  if (meeting.status !== 'active') {
    return res.status(400).json({ error: 'Cannot send message to ended meeting' });
  }

  // Fix C: gateway 未就绪时直接拒绝投递（消息会在会议里无声丢失，必须显式失败让调用方重发）
  const gwForMsg = getGateway();
  if (!gwForMsg.isReady) {
    try { await gwForMsg.waitForReady(10000); } catch { /* 保持未就绪则拒绝 */ }
  }
  if (!gwForMsg.isReady) {
    log.warn(`Message to ${req.params.id} rejected: OpenClaw gateway not connected`);
    return res.status(503).json({ error: 'OpenClaw gateway 未连接，消息未投递（请确认 OpenClaw 已启动后重发）' });
  }

  const { message, fromAgentId, targetAgentIds } = req.body;
  if (!message || typeof message !== 'string') return res.status(400).json({ error: 'message required' });
  if (message.length > 10000) {
    return res.status(400).json({ error: 'Message too long (max 10000 chars)' });
  }
  if (fromAgentId !== undefined && (typeof fromAgentId !== 'string' || fromAgentId.length > 50)) {
    return res.status(400).json({ error: 'Invalid fromAgentId' });
  }
  // Optional: limit this round to a chosen subset of meeting members
  let targetAgentsFilter = null;
  if (targetAgentIds !== undefined) {
    if (!Array.isArray(targetAgentIds) || targetAgentIds.length === 0 ||
        !targetAgentIds.every(id => typeof id === 'string' && meeting.agentIds.includes(id))) {
      return res.status(400).json({ error: 'Invalid targetAgentIds: must be a non-empty array of meeting members' });
    }
    targetAgentsFilter = new Set(targetAgentIds);
  }

  const roundId = randomUUID();

  // C8 Fix: Sanitize meeting message to prevent context tag injection
  const safeMessage = sanitizeContextTags(message);

  // Record user/initiator message
  meeting.messages.push({
    role: fromAgentId ? 'agent' : 'user',
    agentId: fromAgentId || 'user',
    text: safeMessage,
    timestamp: Date.now(),
  });

  // H7 Fix: Cap messages array — keep first 10 + last 190
  if (meeting.messages.length > MAX_MESSAGES_PER_MEETING) {
    const first10 = meeting.messages.slice(0, 10);
    const last190 = meeting.messages.slice(-(MAX_MESSAGES_PER_MEETING - 10));
    meeting.messages = [...first10, ...last190];
  }

  await persistMeeting(meeting);

  // Send to chosen members only (targetAgentIds), otherwise all agents in meeting
  const targetAgents = targetAgentsFilter
    ? meeting.agentIds.filter(id => targetAgentsFilter.has(id))
    : fromAgentId
      ? meeting.agentIds.filter(id => id !== fromAgentId)
      : meeting.agentIds;

  // Return immediately - processing happens in background
  res.json({ status: 'accepted', roundId, targetAgents: targetAgents.length });

  // Process agents in background
  const wss = req.app.locals.wss;
  setImmediate(async () => {
    try { await withMutex(`meeting:${meeting.id}`, async () => {
      const results = [];

      // Sequential: each agent sees previous agents' responses (real discussion)
      for (let agentIndex = 0; agentIndex < targetAgents.length; agentIndex++) {
      // Stop if meeting was ended while agents are still being processed
      if (meeting.status === 'ended' || meeting._cancelRequested) { log.info('Meeting ended, aborting remaining agents'); break; }
      const agentId = targetAgents[agentIndex];

      // Rebuild context each iteration so new responses are visible
      const recentHistory = meeting.messages.slice(-20).map(m => {
        const sender = m.agentId === 'user' ? '用户' : m.agentId;
        return `[${sender}]: ${m.text}`;
      }).join('\n');

      const safeTopic = sanitizeContextTags(meeting.topic);
      const meetingPrompt = `[会议模式] 主题: <user_topic>${safeTopic}</user_topic>
参会成员: ${meeting.agentIds.join(', ')}

最近对话:
${recentHistory}

请根据你的专长回应会议中的讨论。注意其他成员已经发表的观点，不要重复，提出你的独特视角。请严格按以下格式输出（必须包含两个标记，先写思考过程，再写结论）：

【思考过程】
（在这里写出你的分析推理过程，尽量具体，不超过500字）

【结论】
（在这里写出你的最终回答，不超过200字，简洁明确）`;

      const agentSessionKey = getAgentSessionKey(agentId, `meeting:${meeting.id}`);
      const sentAt = Date.now();
      const agentPromise = chatAgent(agentId, meetingPrompt, null, { traceId: req.traceId, scope: `meeting:${meeting.id}` });

      try {
        // P0 Fix #3: Add timeout for agent response
        const result = await Promise.race([
          agentPromise,
          new Promise((_, reject) =>
            setTimeout(() => reject(new Error('Agent response timeout')), DEPT_RESPONSE_TIMEOUT)
          )
        ]);
        const reply = result.success ? result.reply : `[Error] ${result.error}`;

        // Split reply into reasoning + conclusion for display
        const { reasoning, conclusion } = parseAgentReply(reply);

        // Record agent response — next agent will see this
        meeting.messages.push({
          role: 'agent',
          agentId,
          text: reply,
          reasoning,
          conclusion,
          timestamp: Date.now(),
        });

        // H7 Fix: Cap messages array — keep first 10 + last 190
        if (meeting.messages.length > MAX_MESSAGES_PER_MEETING) {
          const first10 = meeting.messages.slice(0, 10);
          const last190 = meeting.messages.slice(-(MAX_MESSAGES_PER_MEETING - 10));
          meeting.messages = [...first10, ...last190];
        }

        // P0 Fix #5: Move persistMeeting inside withMutex
        await persistMeeting(meeting);

        results.push({ agentId, reply, success: result.success });

        // Broadcast agent response immediately via WebSocket
        if (wss) {
          safeBroadcast(wss, {
            event: 'meeting:agent-response',
            data: {
              meetingId: meeting.id,
              agentId,
              text: reply,
              reasoning,
              conclusion,
              roundId,
              agentIndex,
              totalAgents: targetAgents.length,
              timestamp: Date.now(),
            },
          });
        }
      } catch (err) {
        // Handle timeout and rate-limit errors specifically
        const isTimeout = err.message.includes('timeout');
        const isRateLimit = err.message.includes('429') || /rate.?limit/i.test(err.message);
        const errorReply = isTimeout
          ? `[Timeout] ${agentId} 超过180秒未响应，后台等待迟到回复（最长10分钟）`
          : isRateLimit
            ? `[限流] ${agentId} 被限流，跳过`
            : `[Error] ${err.message}`;

        log.info(`Agent ${agentId} ${isTimeout ? 'timed out' : isRateLimit ? 'rate-limited' : 'error'}: ${err.message}`);

        // Record error in messages
        meeting.messages.push({
          role: 'agent',
          agentId,
          text: errorReply,
          timestamp: Date.now(),
        });

        // H7 Fix: Cap messages array — keep first 10 + last 190
        if (meeting.messages.length > MAX_MESSAGES_PER_MEETING) {
          const first10 = meeting.messages.slice(0, 10);
          const last190 = meeting.messages.slice(-(MAX_MESSAGES_PER_MEETING - 10));
          meeting.messages = [...first10, ...last190];
        }

        // P0 Fix #5: Move persistMeeting inside withMutex
        await persistMeeting(meeting);

        results.push({ agentId, reply: errorReply, success: false });

        // Broadcast error via WebSocket
        if (wss) {
          safeBroadcast(wss, {
            event: 'meeting:agent-response',
            data: {
              meetingId: meeting.id,
              agentId,
              text: errorReply,
              roundId,
              agentIndex,
              totalAgents: targetAgents.length,
              timestamp: Date.now(),
              timeout: isTimeout
            },
          });
        }

        // Fix A: 超时后 run 仍在 OpenClaw 侧继续跑，回复不能被静默丢弃 — 后台认领
        if (isTimeout) {
          claimLateReply(meeting, agentId, agentSessionKey, agentPromise, sentAt, wss, roundId);
        }
      }
    }

    // Broadcast round complete
    if (wss) {
      safeBroadcast(wss, {
        event: 'meeting:round-complete',
        data: {
          meetingId: meeting.id,
          roundId,
          messageCount: meeting.messages.length,
          results,
        },
        timestamp: new Date().toISOString(),
      });
    }
    }, { timeout: MEETING_ROUND_MUTEX_TIMEOUT_MS });
    } catch (err) {
      // Fix B: mutex 排队超时/队列满时不再静默吞掉 — 必须在会议里留下痕迹
      log.error(`Message round error: ${err.message}`);
      try {
        const sysMsg = `[系统] 消息处理失败：${err.message}（未投递，请稍后重发）`;
        meeting.messages.push({ role: 'agent', agentId: 'system', text: sysMsg, timestamp: Date.now() });
        await persistMeeting(meeting);
        if (wss) {
          safeBroadcast(wss, {
            event: 'meeting:agent-response',
            data: { meetingId: meeting.id, agentId: 'system', text: sysMsg, timestamp: Date.now() },
          });
        }
      } catch { /* ignore */ }
    }
  });
});

/**
 * POST /api/meetings/:id/participants
 * Add an agent to an active meeting (mid-meeting).
 * Body: { agentId: string }
 */
router.post('/:id/participants', async (req, res) => {
  if (!VALID_MEETING_ID.test(req.params.id)) {
    return res.status(400).json({ error: 'Invalid meeting ID format' });
  }
  const meeting = meetings.get(req.params.id);
  if (!meeting) return res.status(404).json({ error: 'Meeting not found' });
  if (meeting.status !== 'active') {
    return res.status(400).json({ error: 'Cannot add participant to ended meeting' });
  }

  const { agentId } = req.body;
  if (!agentId || typeof agentId !== 'string' || agentId.length > 50) {
    return res.status(400).json({ error: 'agentId required' });
  }
  if (meeting.agentIds.includes(agentId)) {
    return res.status(400).json({ error: 'Agent already in meeting' });
  }

  meeting.agentIds.push(agentId);
  await persistMeeting(meeting);
  recordAudit({ action: 'meeting:add-participant', target: meeting.id, details: { agentId }, ip: req.ip });

  meeting.messages.push({
    role: 'system',
    agentId: 'system',
    text: `[加入会议] ${agentId} 加入了会议`,
    timestamp: Date.now(),
  });
  await persistMeeting(meeting);

  res.json({ success: true, meetingId: meeting.id, agentIds: meeting.agentIds });
});

/**
 * Helper: Generate markdown meeting minutes
 */
function generateMeetingMinutes(meeting) {
  const startTime = new Date(meeting.createdAt);
  const endTime = new Date(meeting.endedAt || Date.now());
  const duration = Math.round((endTime.getTime() - startTime.getTime()) / 1000 / 60);

  let markdown = `# 会议纪要: ${meeting.topic}\n\n`;
  markdown += `**时间**: ${startTime.toLocaleString('zh-CN', { hour12: false })} - ${endTime.toLocaleString('zh-CN', { hour12: false, timeStyle: 'short' })}\n`;
  markdown += `**时长**: ${duration} 分钟\n`;
  markdown += `**参会成员**: ${meeting.agentIds.join(', ')}\n`;
  markdown += `**发起成员**: ${meeting.initiatorAgentId}\n\n`;
  markdown += `---\n\n## 会议记录\n\n`;

  // BUG3 fix: only real speaker messages (user/agent) are listed as 发言;
  // system records (join/leave, negotiation, action items) go to a
  // separate section instead of being framed as a speaker's words.
  const speakerEntries = [];
  const systemEntries = [];
  meeting.messages.forEach((msg, i) => {
    const time = new Date(msg.timestamp).toLocaleTimeString('zh-CN', { hour: '2-digit', minute: '2-digit', hour12: false });
    const isSystem = msg.role === 'system' || msg.agentId === 'system' || msg.agentId === 'action-items' || msg.agentId === 'negotiation';
    if (isSystem) {
      systemEntries.push(`### ${i + 1}. [${time}] 系统\n\n${msg.text}\n\n`);
    } else {
      const sender = msg.role === 'user' || msg.agentId === 'user' ? '用户' : msg.agentId;
      speakerEntries.push(`### ${i + 1}. [${time}] ${sender}\n\n${msg.text}\n\n`);
    }
  });
  if (speakerEntries.length > 0) {
    markdown += speakerEntries.join('');
  }
  if (systemEntries.length > 0) {
    markdown += `---\n\n## 系统记录（协商 / 决议 / 加入退出）\n\n`;
    markdown += systemEntries.join('');
  }

  markdown += `---\n\n`;
  markdown += `**会议ID**: ${meeting.id}\n`;
  markdown += `**生成时间**: ${new Date().toLocaleString('zh-CN', { hour12: false })}\n`;

  return markdown;
}

/**
 * POST /api/meetings/:id/end
 * End a meeting and optionally export to Google Drive
 */
router.post('/:id/end', async (req, res) => {
  if (!VALID_MEETING_ID.test(req.params.id)) {
    return res.status(400).json({ error: 'Invalid meeting ID format' });
  }
  const meeting = meetings.get(req.params.id);
  if (!meeting) return res.status(404).json({ error: 'Meeting not found' });

  let actionItemsSuccess = null;
  let actionItemsError = null;

  // 幂等：已结束会议直接返回，避免重复 extract/persist/broadcast/导出
  if (meeting.status === 'ended') {
    return res.json({ success: true, alreadyEnded: true, driveResult: null, actionItems: { success: null, note: 'already-ended' } });
  }

  // Fix 3(rev): 结束标记先行 — round 循环在 for 顶部检查 status/_cancelRequested 自然 break，
  // 无需再与 round mutex 争锁（原实现默认 30s 超时会 500）。
  meeting._cancelRequested = true;
  clearLateReplyTimers(meeting);
  meeting.status = 'ended';
  meeting.endedAt = Date.now();
  await persistMeeting(meeting);
  log.info(`Ended ${meeting.id}: ${meeting.topic}`);

  recordAudit({ action: 'meeting:end', target: meeting.id, details: { topic: meeting.topic }, ip: req.ip });

  // P0 Fix #4：action items 提取改为锁外 fire-and-forget（不再阻塞结束响应）；
  // 原实现 await 在 mutex 内且 chatAgent 无超时，gateway 卡死时会拖死结束请求。
  const wss = req.app.locals.wss;
  Promise.race([
    extractActionItems(meeting, wss, req.traceId).then(() => { actionItemsSuccess = true; }),
    new Promise((_, reject) => setTimeout(() => reject(new Error('Action items extraction timeout')), 180000)),
  ]).catch((err) => {
    actionItemsSuccess = false;
    actionItemsError = err.message;
    log.error(`Action item extraction failed: ${err.message}`);
    if (wss) {
      safeBroadcast(wss, {
        event: 'meeting:action-items',
        data: { meetingId: meeting.id, actionItems: [], error: err.message },
        timestamp: new Date().toISOString(),
      });
    }
  });

  // BUG2 fix: keep ended meetings in memory + on disk so history stays
  // visible; disk cleanup prunes files older than 30 days.

  // Broadcast meeting:end event to WebSocket clients
  try {
    const wss = req.app.locals.wss;
    if (wss) {
      safeBroadcast(wss, {
        event: 'meeting:end',
        data: {
          meetingId: meeting.id,
          agentIds: meeting.agentIds
        },
        timestamp: new Date().toISOString()
      });
    }
  } catch (err) {
    log.error(`WS broadcast error: ${err.message}`);
  }

  let driveResult = null;
  let driveExportSuccess = true;
  let driveExportError = null;

  // Try to export to Google Drive if auth is available (best-effort, non-blocking)
  if (hasDriveAuth()) {
    try {
      const driveConfig = getDriveConfig();
      const drive = getDriveClient(driveConfig);
      const folderId = await getOrCreateBackupFolder(drive, driveConfig);

      // Generate meeting minutes
      const markdown = generateMeetingMinutes(meeting);
      const timestamp = new Date().toISOString().replace(/[:.]/g, '-').substring(0, 19);
      const filename = `会议纪要_${meeting.topic.substring(0, 20)}_${timestamp}.md`;

      // Upload to Drive
      const buffer = Buffer.from(markdown, 'utf8');
      const fileMetadata = {
        name: filename,
        parents: [folderId]
      };
      const media = {
        mimeType: 'text/markdown',
        body: Readable.from(buffer)
      };

      const file = await drive.files.create({
        resource: fileMetadata,
        media: media,
        fields: 'id, name, webViewLink'
      });

      driveResult = {
        success: true,
        fileId: file.data.id,
        fileName: file.data.name,
        webViewLink: file.data.webViewLink
      };

      log.info(`Exported to Drive: ${filename} (${file.data.id})`);

      // Send notification
      notify({
        severity: 'info',
        category: 'meeting',
        title: '会议纪要已导出',
        body: `会议 "${meeting.topic}" 的纪要已自动导出到 Google Drive`,
        actionUrl: file.data.webViewLink
      });
    } catch (error) {
      driveExportSuccess = false;
      driveExportError = error.message;
      log.error(`Drive export failed (non-fatal): ${error.message}`);
      // Non-fatal: meeting still ends successfully, but return error status
      driveResult = {
        success: false,
        error: error.message
      };
    }
  }

  res.json({
    success: true,
    driveResult,
    actionItems: {
      success: actionItemsSuccess,
      error: actionItemsError
    }
  });
});

/**
 * Extract action items from meeting transcript using AI
 */
async function extractActionItems(meeting, wss, traceId) {
  if (meeting.messages.length < 3) return; // Too short

  // Build transcript
  const transcript = meeting.messages.map(m => {
    const sender = m.agentId === 'user' ? 'User' : m.agentId;
    return `[${sender}]: ${m.text}`;
  }).join('\n');

  const safeTopic = sanitizeContextTags(meeting.topic);
  const prompt = `Analyze this meeting transcript and extract action items.

Meeting topic: <user_topic>${safeTopic}</user_topic>
Departments: ${meeting.agentIds.join(', ')}

Transcript:
${transcript.substring(0, 8000)}

Respond with ONLY a JSON array of action items:
[{"task": "description", "owner": "department_id", "priority": "high/medium/low", "deadline_hint": "suggested timeframe"}]

Extract 3-8 action items. Use actual department IDs from the transcript. Be specific and actionable.`;

  try {
    // Use the first department to extract (or a specific dept if available)
    const extractorAgent = meeting.agentIds[0];
    const result = await chatAgent(extractorAgent, prompt, null, { traceId, scope: `meeting:${meeting.id}` });

    if (result.success && result.reply) {
      const jsonMatch = result.reply.match(/\[[\s\S]*?\]/);
      if (jsonMatch) {
        const actionItems = JSON.parse(jsonMatch[0]);
        if (!Array.isArray(actionItems)) throw new Error('Expected JSON array');
        meeting.actionItems = actionItems;

        // Record in meeting messages (null-safe field access)
        meeting.messages.push({
          role: 'system', agentId: 'action-items',
          text: `[Action Items Extracted]\n${actionItems.map((item, i) =>
            `${i+1}. [${String(item.priority || 'medium').toUpperCase()}] ${String(item.task || '(no task)')} (Owner: ${String(item.owner || 'unassigned')}${item.deadline_hint ? ', ' + String(item.deadline_hint) : ''})`
          ).join('\n')}`,
          timestamp: Date.now()
        });

        await persistMeeting(meeting);

        // Broadcast to UI
        if (wss) {
          safeBroadcast(wss, {
            event: 'meeting:action-items',
            data: { meetingId: meeting.id, actionItems },
            timestamp: new Date().toISOString()
          });
        }

        log.info(`Extracted ${actionItems.length} action items for ${meeting.id}`);
      }
    }
  } catch (err) {
    log.error(`Action item extraction error: ${err.message}`);
  }
}

/**
 * GET /api/meetings/:id/action-items
 * Get action items for a meeting
 */
router.get('/:id/action-items', (req, res) => {
  if (!VALID_MEETING_ID.test(req.params.id)) {
    return res.status(400).json({ error: 'Invalid meeting ID format' });
  }
  const meeting = meetings.get(req.params.id);
  if (!meeting) return res.status(404).json({ error: 'Meeting not found' });
  res.json({ actionItems: meeting.actionItems || [], meetingId: meeting.id });
});

/**
 * POST /api/meetings/:id/negotiate
 * Start negotiation mode - departments debate, vote, and reach consensus
 */
router.post('/:id/negotiate', async (req, res) => {
  const { id } = req.params;
  if (!VALID_MEETING_ID.test(id)) {
    return res.status(400).json({ error: 'Invalid meeting ID format' });
  }
  const { proposal, maxRounds = 3, targetAgentIds } = req.body;
  const meeting = meetings.get(id);
  if (!meeting || meeting.status !== 'active') {
    return res.status(404).json({ error: 'Meeting not found or not active' });
  }

  // Validate
  if (!proposal || typeof proposal !== 'string' || proposal.length > 5000) {
    return res.status(400).json({ error: 'Invalid proposal' });
  }

  // Optional: only these members participate in the negotiation
  let participantAgents = null;
  if (targetAgentIds !== undefined) {
    if (!Array.isArray(targetAgentIds) || targetAgentIds.length === 0 ||
        !targetAgentIds.every(id => typeof id === 'string' && meeting.agentIds.includes(id))) {
      return res.status(400).json({ error: 'Invalid targetAgentIds: must be a non-empty array of meeting members' });
    }
    participantAgents = meeting.agentIds.filter(id => targetAgentIds.includes(id));
  }

  const roundsCapped = Math.min(Math.max(1, maxRounds), 5);

  // Return immediately, process in background
  const negotiationId = `neg_${Date.now().toString(36)}`;
  recordAudit({ action: 'meeting:negotiate', target: id, details: { proposal: proposal.substring(0, 100), maxRounds: roundsCapped }, ip: req.ip });
  res.json({ status: 'accepted', negotiationId, maxRounds: roundsCapped });

  // Run negotiation rounds in background
  // P0 Fix #8: Add 10-minute total timeout for entire negotiation
  Promise.resolve(withMutex(`meeting:${meeting.id}`, async () => {
    try {
      await Promise.race([
        runNegotiation(meeting, proposal, roundsCapped, negotiationId, req.app.locals.wss, req.traceId, participantAgents),
        new Promise((_, reject) =>
          setTimeout(() => reject(new Error('Negotiation timeout')), NEGOTIATION_TIMEOUT)
        )
      ]);
    } catch (err) {
      if (err.message.includes('timeout')) {
        log.error('Negotiation timed out after 10 minutes');
        meeting.messages.push({
          role: 'system', agentId: 'negotiation',
          text: '[Negotiation Timeout] Process exceeded 10 minutes and was terminated',
          timestamp: Date.now(), negotiationId
        });
        persistMeeting(meeting);

        broadcastToMeeting(req.app.locals.wss, meeting.id, 'meeting:negotiation-end', {
          meetingId: meeting.id, negotiationId, result: 'timeout',
          reason: 'Exceeded 10 minute limit'
        });
      } else {
        throw err;
      }
    }
  })).catch(err => log.error(`Negotiation error: ${err.message}`));
});

/**
 * Run negotiation rounds: each dept evaluates proposal and votes
 */
async function runNegotiation(meeting, proposal, maxRounds, negotiationId, wss, traceId, participantAgents) {
  const targetAgents = participantAgents || meeting.agentIds;
  let currentProposal = sanitizeContextTags(proposal);
  let round = 0;
  const positions = {}; // { agentId: { stance: 'agree'|'disagree'|'modify', reason, suggestion } }

  // Record proposal in meeting messages
  meeting.messages.push({
    role: 'system', agentId: 'negotiation',
    text: `[Negotiation Started] Proposal: ${proposal}`,
    timestamp: Date.now(), negotiationId
  });
  persistMeeting(meeting);

  // Broadcast negotiation start
  broadcastToMeeting(wss, meeting.id, 'meeting:negotiation-start', {
    meetingId: meeting.id, negotiationId, proposal, maxRounds, agentIds: targetAgents
  });

  while (round < maxRounds) {
    round++;
    const roundPositions = {};

    // Each department evaluates the proposal
    for (const agentId of targetAgents) {
      const prompt = round === 1
        ? `[Negotiation Mode - Round ${round}/${maxRounds}]
You are evaluating this proposal: "${currentProposal}"

Based on your department's expertise, respond with EXACTLY this JSON format:
{"stance": "agree" or "disagree" or "modify", "reason": "your reasoning in 1-2 sentences", "suggestion": "your counter-proposal or modification if stance is modify/disagree, empty string if agree"}

Be concise. Consider trade-offs from your department's perspective.`
        : `[Negotiation Mode - Round ${round}/${maxRounds}]
Previous positions from other departments:
${Object.entries(positions).map(([d, p]) => `- ${d}: ${p.stance} - ${p.reason}`).join('\n')}

Current proposal: "${currentProposal}"

Based on your department's expertise and considering other departments' positions, respond with EXACTLY this JSON format:
{"stance": "agree" or "disagree" or "modify", "reason": "your reasoning in 1-2 sentences", "suggestion": "your counter-proposal or modification if stance is modify/disagree, empty string if agree"}

Try to find common ground. Be concise.`;

      try {
        const result = await chatAgent(agentId, prompt, null, { traceId, scope: `meeting:${meeting.id}` });
        let parsed;
        if (!result.success || !result.reply) {
          parsed = { stance: 'abstain', reason: result.error || 'No response', suggestion: '' };
        } else {
          try {
            // Try to extract JSON from response
            const jsonMatch = result.reply.match(/\{[\s\S]*?\}/);
            parsed = jsonMatch ? JSON.parse(jsonMatch[0]) : { stance: 'abstain', reason: result.reply, suggestion: '' };
          } catch {
            parsed = { stance: 'abstain', reason: result.reply.substring(0, 200), suggestion: '' };
          }
        }

        roundPositions[agentId] = parsed;
        positions[agentId] = parsed;

        // Record in meeting messages (null-safe field access)
        meeting.messages.push({
          role: 'agent', agentId,
          text: `[Round ${round}] ${String(parsed.stance || 'abstain').toUpperCase()}: ${parsed.reason || ''}${parsed.suggestion ? '\nSuggestion: ' + parsed.suggestion : ''}`,
          timestamp: Date.now(), negotiationId
        });
        persistMeeting(meeting);

        // Broadcast each dept's position
        broadcastToMeeting(wss, meeting.id, 'meeting:negotiation-vote', {
          meetingId: meeting.id, negotiationId, round, agentId,
          stance: parsed.stance, reason: parsed.reason, suggestion: parsed.suggestion
        });
      } catch (err) {
        roundPositions[agentId] = { stance: 'abstain', reason: 'Error: ' + err.message, suggestion: '' };
      }
    }

    // Check consensus
    const stances = Object.values(roundPositions).map(p => p.stance);
    const agreeCount = stances.filter(s => s === 'agree').length;
    const total = stances.length;

    // Broadcast round summary
    broadcastToMeeting(wss, meeting.id, 'meeting:negotiation-round', {
      meetingId: meeting.id, negotiationId, round, maxRounds,
      positions: roundPositions,
      consensus: agreeCount === total,
      agreeCount, total
    });

    if (agreeCount === total) {
      // Consensus reached!
      meeting.messages.push({
        role: 'system', agentId: 'negotiation',
        text: `[Consensus Reached in Round ${round}] All ${total} agents agree on: ${currentProposal}`,
        timestamp: Date.now(), negotiationId
      });
      persistMeeting(meeting);

      broadcastToMeeting(wss, meeting.id, 'meeting:negotiation-end', {
        meetingId: meeting.id, negotiationId, result: 'consensus', round,
        finalProposal: currentProposal, positions
      });
      return;
    }

    // P0 Fix #7: Randomly select modification to avoid first-dept bias
    if (agreeCount >= total * 0.5) {
      const modifications = Object.values(roundPositions)
        .filter(p => p.stance === 'modify' && p.suggestion)
        .map(p => p.suggestion);
      if (modifications.length > 0) {
        const randomIndex = Math.floor(Math.random() * modifications.length);
        currentProposal = modifications[randomIndex];
      }
    }
  }

  // Max rounds reached without full consensus
  const finalStances = Object.entries(positions);
  const agreeCount = finalStances.filter(([,p]) => p.stance === 'agree').length;
  const result = agreeCount > finalStances.length / 2 ? 'majority' : 'no-consensus';

  meeting.messages.push({
    role: 'system', agentId: 'negotiation',
    text: `[Negotiation Complete - ${result === 'majority' ? 'Majority Agreement' : 'No Consensus'}] After ${maxRounds} rounds: ${agreeCount}/${finalStances.length} agree`,
    timestamp: Date.now(), negotiationId
  });
  persistMeeting(meeting);

  broadcastToMeeting(wss, meeting.id, 'meeting:negotiation-end', {
    meetingId: meeting.id, negotiationId, result, round: maxRounds,
    finalProposal: currentProposal, positions,
    agreeCount, total: finalStances.length
  });
}

/**
 * Broadcast message to all authenticated WebSocket clients
 */
function broadcastToMeeting(wss, meetingId, event, data) {
  if (!wss) return;
  safeBroadcast(wss, { event, data, timestamp: new Date().toISOString() });
}

/**
 * POST /api/meetings/auto
 * 自动开会：建会后主持人发起、其余 agent 依次回应，多轮自主讨论。
 * Body: { topic: string, agentIds: string[], initiatorAgentId?: string, rounds?: number }
 */
router.post('/auto', async (req, res) => {
  const { topic, agentIds, initiatorAgentId, rounds } = req.body;
  if (!topic || typeof topic !== 'string' || !Array.isArray(agentIds) || agentIds.length < 2) {
    return res.status(400).json({ error: 'topic and at least 2 agentIds required' });
  }
  if (topic.length > 500) {
    return res.status(400).json({ error: 'topic must be 500 characters or less' });
  }
  if (agentIds.length > 20 || !agentIds.every(id => typeof id === 'string' && id.length <= 50)) {
    return res.status(400).json({ error: 'invalid agentIds' });
  }

  const roundsCapped = Math.min(Math.max(1, parseInt(rounds, 10) || 3), 8);
  const initiator = typeof initiatorAgentId === 'string' && agentIds.includes(initiatorAgentId)
    ? initiatorAgentId
    : agentIds[0];

  const result = await withMutex('meeting-creation', async () => {
    // Auto-end all existing active meetings before creating a new one (only 1 active at a time)
    const activeMeetings = [...meetings.values()].filter(m => m.status === 'active');
    for (const oldMtg of activeMeetings) {
      oldMtg.status = 'ended';
      oldMtg.endedAt = Date.now();
      await persistMeeting(oldMtg);
      log.info(`Auto-ended ${oldMtg.id} (new auto meeting starting)`);
      recordAudit({ action: 'meeting:auto-end', target: oldMtg.id, details: { reason: 'superseded' }, ip: req.ip });
    }
    const meetingId = 'mtg_' + randomUUID().replace(/-/g, '').substring(0, 12);
    const meeting = {
      id: meetingId,
      topic,
      agentIds,
      initiatorAgentId: initiator,
      messages: [],
      status: 'active',
      createdAt: Date.now(),
      mode: 'auto',
    };
    meetings.set(meetingId, meeting);
    await persistMeeting(meeting);
    log.info(`Auto meeting created ${meetingId}: ${topic} with ${agentIds.join(', ')}`);
    recordAudit({ action: 'meeting:auto:create', target: meetingId, details: { topic, agentIds, rounds: roundsCapped }, ip: req.ip });
    return { error: false, meeting, meetingId };
  });

  if (result.error) {
    return res.status(result.status).json(result.data);
  }
  const { meeting, meetingId } = result;

  const wss = req.app.locals.wss;
  if (wss) {
    safeBroadcast(wss, {
      event: 'meeting:start',
      data: { meetingId, topic: meeting.topic, agentIds: meeting.agentIds, mode: 'auto' },
      timestamp: new Date().toISOString(),
    });
  }

  res.json({
    success: true,
    meetingId,
    topic: meeting.topic,
    agentIds: meeting.agentIds,
    initiatorAgentId: initiator,
    rounds: roundsCapped,
  });

  // Process discussion in background
  setImmediate(async () => {
    try {
      await withMutex(`meeting:${meetingId}`, () => runAutoDiscussion(meeting, roundsCapped, initiator, wss, req.traceId));
    } catch (err) {
      log.error(`Auto meeting discussion error: ${err.message}`);
    }
  });
});

/**
 * Run autonomous multi-round discussion for an auto meeting.
 * Host (initiator) drives each round; remaining agents respond sequentially.
 */
async function runAutoDiscussion(meeting, rounds, initiator, wss, traceId) {
  const others = meeting.agentIds.filter(id => id !== initiator);
  const safeTopic = sanitizeContextTags(meeting.topic);

  const buildRecent = (limit = 12) => meeting.messages.slice(-limit).map(m => {
    const sender = m.agentId === 'user' ? '用户' : m.agentId;
    return `[${sender}]: ${m.text}`;
  }).join('\n');

  const cap = () => {
    if (meeting.messages.length > MAX_MESSAGES_PER_MEETING) {
      meeting.messages = [...meeting.messages.slice(0, 10), ...meeting.messages.slice(-(MAX_MESSAGES_PER_MEETING - 10))];
    }
  };

  const callOne = (agentId, prompt) => Promise.race([
    chatAgent(agentId, prompt, null, { traceId, scope: `meeting:${meeting.id}` }),
    new Promise((_, reject) => setTimeout(() => reject(new Error('Agent response timeout')), DEPT_RESPONSE_TIMEOUT)),
  ]);

  for (let round = 1; round <= rounds; round++) {
    // 1. 主持人推进讨论
    const hostPrompt = `[会议模式-自主讨论] 主题: <user_topic>${safeTopic}</user_topic>
参会成员: ${meeting.agentIds.join(', ')}
现在是第 ${round}/${rounds} 轮。你作为会议主持人，基于下面的最近对话，提出一个推动 ROI 方案讨论的关键问题或观点（不要重复已讨论内容）。简洁，不超过150字。

最近对话:
${buildRecent()}`;

    const hostResult = await callOne(initiator, hostPrompt);
    const hostText = hostResult?.success ? hostResult.reply : `[Error] ${hostResult?.error || 'no response'}`;
    meeting.messages.push({ role: 'agent', agentId: initiator, text: hostText, timestamp: Date.now() });
    cap();
    await persistMeeting(meeting);
    broadcastToMeeting(wss, meeting.id, 'meeting:agent-response', {
      meetingId: meeting.id, agentId: initiator, text: hostText, round,
      agentIndex: 0, totalAgents: meeting.agentIds.length, timestamp: Date.now(),
    });

    // 2. 其余 agent 依次回应
    for (let i = 0; i < others.length; i++) {
      if (meeting.status === 'ended') { log.info('Meeting ended, aborting remaining agents'); break; }
      const agentId = others[i];
      const prompt = `[会议模式] 主题: <user_topic>${safeTopic}</user_topic>
参会成员: ${meeting.agentIds.join(', ')}
第 ${round}/${rounds} 轮。请根据你的专长回应会议中关于 ROI 方案的讨论，注意其他成员已发表的观点，不要重复，提出你的独特视角。简洁，不超过200字。

最近对话:
${buildRecent()}`;

      const result = await callOne(agentId, prompt);
      const reply = result?.success ? result.reply : `[Error] ${result?.error || 'no response'}`;
      meeting.messages.push({ role: 'agent', agentId, text: reply, timestamp: Date.now() });
      cap();
      await persistMeeting(meeting);
      broadcastToMeeting(wss, meeting.id, 'meeting:agent-response', {
        meetingId: meeting.id, agentId, text: reply, round,
        agentIndex: i + 1, totalAgents: meeting.agentIds.length, timestamp: Date.now(),
      });
    }
  }

  meeting._cancelRequested = true;
  clearLateReplyTimers(meeting);
  meeting.status = 'ended';
  meeting.endedAt = Date.now();
  await persistMeeting(meeting);
  if (wss) {
    safeBroadcast(wss, {
      event: 'meeting:end',
      data: { meetingId: meeting.id, agentIds: meeting.agentIds },
      timestamp: new Date().toISOString(),
    });
  }
  log.info(`Auto meeting ${meeting.id} finished (${rounds} rounds)`);
}

export default router;
