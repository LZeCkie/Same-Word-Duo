'use strict';

/**
 * Same Word · 双人同词相遇（联网版）
 * ------------------------------------------------------------
 * 零第三方依赖的 Node.js 房间服务器：
 *   1. 提供单页 HTML；
 *   2. 通过原生 WebSocket 实时同步房间状态；
 *   3. 房间只保存在内存中，服务器重启会清空；
 *   4. 所有游戏判定都在服务端完成，客户端无法提前看到对方词语。
 *
 * 启动：node server.js
 * 端口：PORT 环境变量，默认 3000
 */

const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const zlib = require('zlib');
const crypto = require('crypto');
const { URL } = require('url');

const PORT = Number(process.env.PORT) || 3000;
const HOST = process.env.HOST || '0.0.0.0';
const WS_GUID = '258EAFA5-E914-47DA-95CA-C5AB0DC85B11';
const MAX_FRAME_BYTES = 64 * 1024;
const MAX_MESSAGE_BYTES = 8 * 1024;
const MAX_ROOM_AGE_MS = 12 * 60 * 60 * 1000;
const EMPTY_ROOM_TTL_MS = 30 * 60 * 1000;
const CLIENT_HEARTBEAT_MS = 30 * 1000;
const CLEANUP_INTERVAL_MS = 5 * 60 * 1000;
const MAX_WORD_LENGTH = 24;
const CODE_UPPER = 'ABCDEFGHJKLMNPQRSTUVWXYZ';
const CODE_LOWER = 'abcdefghijkmnopqrstuvwxyz';
const CODE_DIGITS = '23456789';
const CODE_ALL = CODE_UPPER + CODE_LOWER + CODE_DIGITS;

const HTML_PATH = path.join(__dirname, 'public', 'index.html');

let htmlRaw;
let htmlGzip;
try {
  htmlRaw = fs.readFileSync(HTML_PATH);
  htmlGzip = zlib.gzipSync(htmlRaw);
} catch (error) {
  console.error('无法读取 public/index.html：', error.message);
  process.exit(1);
}

/** @type {Map<string, object>} 键为小写房间码 */
const rooms = new Map();
/** @type {Set<WSClient>} */
const clients = new Set();

/* ============================================================
   基础工具
   ============================================================ */
function randomIndex(max) {
  return crypto.randomInt(0, max);
}

function randomToken(bytes) {
  return crypto.randomBytes(bytes).toString('hex');
}

function shuffle(array) {
  for (let i = array.length - 1; i > 0; i -= 1) {
    const j = randomIndex(i + 1);
    [array[i], array[j]] = [array[j], array[i]];
  }
  return array;
}

function generateRoomCode() {
  for (let attempt = 0; attempt < 100; attempt += 1) {
    const chars = [
      CODE_UPPER[randomIndex(CODE_UPPER.length)],
      CODE_LOWER[randomIndex(CODE_LOWER.length)],
      CODE_DIGITS[randomIndex(CODE_DIGITS.length)]
    ];
    while (chars.length < 6) {
      chars.push(CODE_ALL[randomIndex(CODE_ALL.length)]);
    }
    const code = shuffle(chars).join('');
    if (!rooms.has(code.toLowerCase())) return code;
  }
  return 'sw' + randomToken(2);
}

function isValidCode(code) {
  return /^[A-Za-z0-9]{6}$/.test(String(code || ''));
}

function charLength(value) {
  return Array.from(String(value || '')).length;
}

function cleanWord(value) {
  return String(value || '')
    .normalize('NFC')
    .replace(/[\u0000-\u001F\u007F]/g, '')
    .trim()
    .replace(/\s+/g, ' ');
}

function nowClock() {
  return new Date().toISOString();
}

function makeCurrent(round, base) {
  return {
    round,
    words: {},
    votes: {},
    base: (Array.isArray(base) ? base : [])
      .map((item) => ({ id: String(item.id || ''), word: String(item.word || '') }))
      .filter((item) => item.id && item.word)
  };
}

function makeRoom(code, player) {
  const now = Date.now();
  return {
    code,
    createdAt: now,
    updatedAt: now,
    startedAt: 0,
    status: 'waiting',
    players: [player],
    round: 1,
    current: makeCurrent(1, []),
    history: [],
    rematchVotes: {}
  };
}

function findPartner(room, player) {
  return room.players.find((candidate) => candidate.id !== player.id) || null;
}

function finalEntry(room) {
  if (!room.history.length) return null;
  return room.history[room.history.length - 1];
}

function settleRoom(room) {
  if (room.status !== 'playing' || !room.current) return false;
  if (room.players.length !== 2) return false;

  const current = room.current;
  const first = current.words[room.players[0].id] || '';
  const second = current.words[room.players[1].id] || '';
  if (!first || !second) return false;

  if (first === second) {
    finishRound(room, 'exact');
    return true;
  }

  const votes = room.players.map((player) => current.votes[player.id] || '');
  if (votes.includes('no')) {
    finishRound(room, 'continue');
    return true;
  }
  if (votes.every((vote) => vote === 'yes')) {
    finishRound(room, 'synonym');
    return true;
  }
  return false;
}

function finishRound(room, result) {
  const current = room.current;
  if (!current) return;

  const entry = {
    round: current.round,
    words: room.players.map((player) => ({
      id: player.id,
      word: current.words[player.id] || ''
    })),
    votes: { ...current.votes },
    result,
    endedAt: Date.now()
  };
  room.history.push(entry);

  if (result === 'continue') {
    const nextRound = current.round + 1;
    room.status = 'playing';
    room.round = nextRound;
    room.current = makeCurrent(nextRound, entry.words);
  } else {
    room.status = 'success';
    room.round = current.round;
    room.current = null;
    room.rematchVotes = {};
  }
}

function resetRoomForRematch(room) {
  room.status = 'playing';
  room.round = 1;
  room.startedAt = Date.now();
  room.current = makeCurrent(1, []);
  room.history = [];
  room.rematchVotes = {};
}

function settleRematch(room) {
  if (room.status !== 'success' || room.players.length !== 2) return false;
  const bothReady = room.players.every((player) => Boolean(room.rematchVotes[player.id]));
  if (!bothReady) return false;
  resetRoomForRematch(room);
  return true;
}

/* ============================================================
   房间视图：每个玩家只收到属于自己视角的数据
   ============================================================ */
function historyWordFor(entry, playerId) {
  const found = entry.words.find((item) => item.id === playerId);
  return found ? found.word : '—';
}

function roomView(room, viewer) {
  const partner = findPartner(room, viewer);
  const current = room.current;
  const bothSubmitted = Boolean(
    current &&
    partner &&
    current.words[viewer.id] &&
    current.words[partner.id]
  );

  let currentView = null;
  if (current) {
    const base = [];
    if (partner) {
      const mine = current.base.find((item) => item.id === viewer.id);
      const theirs = current.base.find((item) => item.id === partner.id);
      if (mine) base.push({ role: '你', word: mine.word });
      if (theirs) base.push({ role: 'TA', word: theirs.word });
    } else {
      current.base.forEach((item) => {
        base.push({
          role: item.id === viewer.id ? '你' : 'TA',
          word: item.word
        });
      });
    }

    currentView = {
      round: current.round,
      myWord: bothSubmitted ? current.words[viewer.id] : '',
      partnerWord: bothSubmitted ? current.words[partner.id] : '',
      mySubmitted: Boolean(current.words[viewer.id]),
      partnerSubmitted: Boolean(partner && current.words[partner.id]),
      bothSubmitted,
      myVote: current.votes[viewer.id] || '',
      partnerVoted: Boolean(partner && current.votes[partner.id]),
      base
    };
  }

  return {
    code: room.code,
    status: room.status,
    round: room.round,
    you: { connected: Boolean(viewer.ws) },
    partner: partner
      ? { connected: Boolean(partner.ws) }
      : null,
    playersCount: room.players.length,
    partnerConnected: Boolean(partner && partner.ws),
    current: currentView,
    history: room.history.map((entry) => ({
      round: entry.round,
      words: [
        { role: '你', word: historyWordFor(entry, viewer.id) },
        { role: 'TA', word: historyWordFor(entry, partner ? partner.id : '') }
      ],
      votes: {
        you: entry.votes[viewer.id] || '',
        ta: partner ? (entry.votes[partner.id] || '') : ''
      },
      result: entry.result,
      endedAt: entry.endedAt
    })),
    rematch: {
      you: Boolean(room.rematchVotes[viewer.id]),
      ta: partner ? Boolean(room.rematchVotes[partner.id]) : false
    },
    updatedAt: room.updatedAt
  };
}

function sendJSON(client, payload) {
  if (!client || !client.ready) return;
  client.sendText(JSON.stringify(payload));
}

function sendError(client, code, message, action) {
  sendJSON(client, {
    type: 'error',
    code,
    message,
    action: action || ''
  });
}

function broadcastRoom(room) {
  for (const player of room.players) {
    if (!player.ws || !player.ws.ready) continue;
    sendJSON(player.ws, {
      type: 'state',
      room: roomView(room, player)
    });
  }
}

function sendWelcome(client, room, player, reason) {
  sendJSON(client, {
    type: 'welcome',
    reason,
    code: room.code,
    playerId: player.id,
    token: player.token,
    room: roomView(room, player)
  });
}

/* ============================================================
   原生 WebSocket 服务端实现（RFC 6455 子集）
   ============================================================ */
class WSClient {
  constructor(socket, request, head) {
    this.socket = socket;
    this.request = request;
    this.buffer = head && head.length ? Buffer.from(head) : Buffer.alloc(0);
    this.ready = true;
    this.closed = false;
    this.closing = false;
    this.isAlive = true;
    this.fragments = [];
    this.fragmentOpcode = 0;
    this.fragmentBytes = 0;
    this.session = null;
    this.onMessage = null;
    this.onClose = null;
    this.messageWindowStartedAt = Date.now();
    this.messageWindowCount = 0;

    socket.setNoDelay(true);
    socket.setKeepAlive(true, 30 * 1000);

    socket.on('data', (chunk) => {
      if (this.closed || this.closing) return;
      this.buffer = this.buffer.length
        ? Buffer.concat([this.buffer, chunk])
        : chunk;
      this.parseFrames();
    });

    socket.on('close', () => {
      this.cleanup();
    });

    socket.on('error', () => {
      this.cleanup();
    });

    if (this.buffer.length) {
      queueMicrotask(() => this.parseFrames());
    }
  }

  cleanup() {
    if (this.closed) return;
    this.closed = true;
    this.ready = false;
    if (typeof this.onClose === 'function') {
      const handler = this.onClose;
      this.onClose = null;
      handler(this);
    }
    this.session = null;
  }

  acceptMessages() {
    const now = Date.now();
    if (now - this.messageWindowStartedAt > 10 * 1000) {
      this.messageWindowStartedAt = now;
      this.messageWindowCount = 0;
    }
    this.messageWindowCount += 1;
    if (this.messageWindowCount > 80) return false;
    return true;
  }

  sendText(text) {
    if (!this.ready || this.closed) return;
    const payload = Buffer.from(String(text), 'utf8');
    if (payload.length > MAX_FRAME_BYTES) return;
    this.writeFrame(0x1, payload);
  }

  ping() {
    if (!this.ready || this.closed) return;
    this.writeFrame(0x9, Buffer.alloc(0));
  }

  pong(payload) {
    if (!this.ready || this.closed) return;
    this.writeFrame(0xA, payload);
  }

  writeFrame(opcode, payload) {
    if (!this.ready || this.closed) return;
    const length = payload.length;
    let header;
    if (length < 126) {
      header = Buffer.alloc(2);
      header[1] = length;
    } else if (length < 65536) {
      header = Buffer.alloc(4);
      header[1] = 126;
      header.writeUInt16BE(length, 2);
    } else {
      header = Buffer.alloc(10);
      header[1] = 127;
      header.writeBigUInt64BE(BigInt(length), 2);
    }
    header[0] = 0x80 | opcode;
    this.socket.write(Buffer.concat([header, payload]));
  }

  sendClose(code, reason) {
    if (this.closed) return;
    const reasonBuffer = Buffer.from(String(reason || '').slice(0, 120), 'utf8');
    const payload = Buffer.alloc(2 + reasonBuffer.length);
    payload.writeUInt16BE(code || 1000, 0);
    reasonBuffer.copy(payload, 2);
    try {
      this.writeFrame(0x8, payload);
    } catch (error) {
      /* 忽略关闭帧写失败 */
    }
  }

  close(code, reason) {
    if (this.closed || this.closing) return;
    this.closing = true;
    this.sendClose(code || 1000, reason || '');
    setTimeout(() => {
      try {
        this.socket.end();
      } catch (error) {
        /* 忽略 */
      }
      setTimeout(() => {
        try {
          this.socket.destroy();
        } catch (error) {
          /* 忽略 */
        }
      }, 120);
    }, 30);
  }

  terminate() {
    this.closing = true;
    try {
      this.socket.destroy();
    } catch (error) {
      /* 忽略 */
    }
  }

  fail(code, reason) {
    this.close(code, reason);
  }

  parseFrames() {
    while (!this.closed && !this.closing) {
      if (this.buffer.length < 2) return;

      const b0 = this.buffer[0];
      const b1 = this.buffer[1];
      const fin = Boolean(b0 & 0x80);
      const opcode = b0 & 0x0f;
      const masked = Boolean(b1 & 0x80);
      let length = b1 & 0x7f;
      let offset = 2;

      if (b0 & 0x70) {
        this.fail(1002, 'Reserved bits');
        return;
      }

      if (length === 126) {
        if (this.buffer.length < offset + 2) return;
        length = this.buffer.readUInt16BE(offset);
        offset += 2;
      } else if (length === 127) {
        if (this.buffer.length < offset + 8) return;
        const bigLength = this.buffer.readBigUInt64BE(offset);
        if (bigLength > BigInt(MAX_FRAME_BYTES)) {
          this.fail(1009, 'Frame too large');
          return;
        }
        length = Number(bigLength);
        offset += 8;
      }

      if (!masked) {
        this.fail(1002, 'Client frame must be masked');
        return;
      }
      if (length > MAX_FRAME_BYTES) {
        this.fail(1009, 'Frame too large');
        return;
      }

      if (this.buffer.length < offset + 4 + length) return;

      const maskKey = this.buffer.subarray(offset, offset + 4);
      offset += 4;
      const payload = this.buffer.subarray(offset, offset + length);
      for (let i = 0; i < payload.length; i += 1) {
        payload[i] ^= maskKey[i % 4];
      }
      const framePayload = Buffer.from(payload);
      this.buffer = this.buffer.subarray(offset + length);

      if (opcode >= 0x8) {
        if (!fin || length > 125) {
          this.fail(1002, 'Invalid control frame');
          return;
        }
        this.handleControlFrame(opcode, framePayload);
        continue;
      }

      if (opcode === 0x0) {
        if (!this.fragmentOpcode) {
          this.fail(1002, 'Unexpected continuation frame');
          return;
        }
        this.fragments.push(framePayload);
        this.fragmentBytes += framePayload.length;
        if (this.fragmentBytes > MAX_MESSAGE_BYTES) {
          this.fail(1009, 'Message too large');
          return;
        }
        if (fin) {
          const full = Buffer.concat(this.fragments);
          const originalOpcode = this.fragmentOpcode;
          this.fragments = [];
          this.fragmentOpcode = 0;
          this.fragmentBytes = 0;
          if (originalOpcode === 0x1) this.handleTextMessage(full);
        }
        continue;
      }

      if (opcode === 0x1) {
        if (this.fragmentOpcode) {
          this.fail(1002, 'Nested fragmented message');
          return;
        }
        if (fin) {
          this.handleTextMessage(framePayload);
        } else {
          this.fragments = [framePayload];
          this.fragmentOpcode = opcode;
          this.fragmentBytes = framePayload.length;
          if (this.fragmentBytes > MAX_MESSAGE_BYTES) {
            this.fail(1009, 'Message too large');
            return;
          }
        }
        continue;
      }

      if (opcode === 0x2) {
        this.fail(1003, 'Binary frames are not supported');
        return;
      }

      this.fail(1002, 'Unsupported opcode');
      return;
    }
  }

  handleControlFrame(opcode, payload) {
    if (opcode === 0x8) {
      this.closing = true;
      this.sendClose(1000, '');
      this.ready = false;
      try {
        this.socket.end();
      } catch (error) {
        /* 忽略 */
      }
      return;
    }
    if (opcode === 0x9) {
      this.pong(payload);
      return;
    }
    if (opcode === 0xA) {
      this.isAlive = true;
    }
  }

  handleTextMessage(buffer) {
    if (buffer.length > MAX_MESSAGE_BYTES) {
      this.fail(1009, 'Message too large');
      return;
    }
    if (!this.acceptMessages()) {
      this.fail(1008, 'Too many messages');
      return;
    }
    this.isAlive = true;
    const text = buffer.toString('utf8');
    if (typeof this.onMessage === 'function') {
      try {
        this.onMessage(text, this);
      } catch (error) {
        console.error('处理 WebSocket 消息失败：', error);
        this.close(1011, 'Internal error');
      }
    }
  }
}

function rejectUpgrade(socket, status, message) {
  try {
    const body = String(message || 'WebSocket upgrade rejected');
    socket.write(
      `HTTP/1.1 ${status || 400} Bad Request\r\n` +
      'Connection: close\r\n' +
      'Content-Type: text/plain; charset=utf-8\r\n' +
      `Content-Length: ${Buffer.byteLength(body)}\r\n\r\n` +
      body
    );
  } catch (error) {
    /* 忽略 */
  }
  socket.destroy();
}

/* ============================================================
   玩家与会话
   ============================================================ */
function addPlayer(room, client) {
  const player = {
    id: randomToken(12),
    token: randomToken(24),
    ws: client,
    joinedAt: Date.now(),
    lastSeen: Date.now()
  };
  room.players.push(player);
  client.session = {
    code: room.code,
    playerId: player.id
  };
  return player;
}

function sessionContext(client) {
  if (!client.session) return null;
  const room = rooms.get(client.session.code.toLowerCase());
  if (!room) return null;
  const player = room.players.find((candidate) => candidate.id === client.session.playerId);
  if (!player) return null;
  return { room, player };
}

function requireSession(client, action) {
  const context = sessionContext(client);
  if (!context) {
    sendError(client, 'NO_ROOM', '你还没有在房间里，先创建或加入一个吧。', action);
    return null;
  }
  return context;
}

function clearAllSessions(room) {
  for (const player of room.players) {
    if (player.ws) {
      player.ws.session = null;
      player.ws = null;
    }
    player.connected = false;
  }
}

function deleteRoom(room, code, message, exceptPlayerId) {
  if (rooms.get(room.code.toLowerCase()) === room) {
    rooms.delete(room.code.toLowerCase());
  }

  for (const player of room.players) {
    if (player.ws && player.ws.ready && player.id !== exceptPlayerId) {
      if (player.ws.session && player.ws.session.playerId === player.id) {
        player.ws.session = null;
      }
      sendJSON(player.ws, {
        type: 'room-closed',
        code: code || 'ROOM_CLOSED',
        message: message || '房间已经关闭。'
      });
    }
    player.ws = null;
    player.connected = false;
  }
}

/* ============================================================
   客户端消息处理
   ============================================================ */
function handleClientMessage(text, client) {
  let message;
  try {
    message = JSON.parse(text);
  } catch (error) {
    sendError(client, 'BAD_MESSAGE', '消息格式不太对。', '');
    return;
  }

  if (!message || typeof message.type !== 'string') {
    sendError(client, 'BAD_MESSAGE', '消息格式不太对。', '');
    return;
  }

  try {
    switch (message.type) {
      case 'create':
        handleCreate(client);
        break;
      case 'join':
        handleJoin(client, message);
        break;
      case 'resume':
        handleResume(client, message);
        break;
      case 'submit':
        handleSubmit(client, message);
        break;
      case 'vote':
        handleVote(client, message);
        break;
      case 'rematch':
        handleRematch(client);
        break;
      case 'leave':
        handleLeave(client);
        break;
      case 'sync':
        handleSync(client);
        break;
      default:
        sendError(client, 'UNKNOWN_ACTION', '这个操作我还没学会。', message.type);
    }
  } catch (error) {
    console.error('处理消息时出错：', error);
    sendError(client, 'SERVER_ERROR', '服务器刚刚打了个小喷嚏，再试一次吧。', message.type);
  }
}

function handleCreate(client) {
  if (client.session) {
    sendError(client, 'ALREADY_IN_ROOM', '你已经在房间里啦。', 'create');
    return;
  }

  const code = generateRoomCode();
  const player = {
    id: randomToken(12),
    token: randomToken(24),
    ws: client,
    joinedAt: Date.now(),
    lastSeen: Date.now()
  };
  const room = makeRoom(code, player);
  room.updatedAt = Date.now();
  rooms.set(code.toLowerCase(), room);
  client.session = { code, playerId: player.id };
  sendWelcome(client, room, player, 'create');
}

function handleJoin(client, message) {
  if (client.session) {
    sendError(client, 'ALREADY_IN_ROOM', '你已经在房间里啦。', 'join');
    return;
  }

  const code = String(message.code || '').trim();
  if (!isValidCode(code)) {
    sendError(client, 'INVALID_CODE', '房间码是 6 位字母或数字，再看一眼？', 'join');
    return;
  }

  const room = rooms.get(code.toLowerCase());
  if (!room) {
    sendError(client, 'ROOM_NOT_FOUND', '没有找到这间小屋，房间码再对一下？', 'join');
    return;
  }

  if (room.players.length >= 2) {
    sendError(client, 'ROOM_FULL', '这间小屋已经坐满两位啦。', 'join');
    return;
  }

  if (room.status !== 'waiting') {
    sendError(client, 'GAME_STARTED', '这一局已经开始啦，等下一次邀请吧。', 'join');
    return;
  }

  const player = addPlayer(room, client);
  room.updatedAt = Date.now();

  if (room.players.length === 2) {
    room.status = 'playing';
    room.startedAt = Date.now();
    room.round = 1;
    room.current = makeCurrent(1, []);
    room.history = [];
    room.rematchVotes = {};
  }

  sendWelcome(client, room, player, 'join');
  broadcastRoom(room);
}

function handleResume(client, message) {
  if (client.session) {
    sendError(client, 'ALREADY_IN_ROOM', '你已经在这个房间里啦。', 'resume');
    return;
  }

  const code = String(message.code || '').trim();
  const playerId = String(message.playerId || '');
  const token = String(message.token || '');
  const room = rooms.get(code.toLowerCase());

  if (!room || !playerId || !token) {
    sendError(client, 'RESUME_FAILED', '之前的座位已经失效，重新加入一次吧。', 'resume');
    return;
  }

  const player = room.players.find(
    (candidate) => candidate.id === playerId && candidate.token === token
  );

  if (!player) {
    sendError(client, 'RESUME_FAILED', '之前的座位已经失效，重新加入一次吧。', 'resume');
    return;
  }

  const oldSocket = player.ws;
  if (oldSocket && oldSocket !== client) {
    oldSocket.session = null;
    sendJSON(oldSocket, {
      type: 'replaced',
      message: '这个座位已经在另一个标签页里打开啦。'
    });
    oldSocket.close(4001, 'Session replaced');
  }

  player.ws = client;
  player.lastSeen = Date.now();
  client.session = { code: room.code, playerId: player.id };
  sendWelcome(client, room, player, 'resume');
  broadcastRoom(room);
}

function handleSubmit(client, message) {
  const context = requireSession(client, 'submit');
  if (!context) return;
  const { room, player } = context;
  const partner = findPartner(room, player);

  if (room.status !== 'playing' || !room.current || !partner) {
    sendError(client, 'GAME_NOT_ACTIVE', '现在还不能提交词语。', 'submit');
    return;
  }

  const expectedRound = Number(message.round);
  if (!Number.isInteger(expectedRound) || expectedRound !== room.current.round) {
    sendError(client, 'STALE_ROUND', '这一轮已经翻篇啦，稍等同步。', 'submit');
    return;
  }

  if (room.current.words[player.id]) {
    sendError(client, 'ALREADY_SUBMITTED', '这个词已经藏好啦。', 'submit');
    return;
  }

  const word = cleanWord(message.word);
  if (!word) {
    sendError(client, 'INVALID_WORD', '先写一个词吧，哪怕只有一个字。', 'submit');
    return;
  }
  if (charLength(word) > MAX_WORD_LENGTH) {
    sendError(client, 'WORD_TOO_LONG', `这个词有点长，最多 ${MAX_WORD_LENGTH} 个字。`, 'submit');
    return;
  }

  room.current.words[player.id] = word;
  player.lastSeen = Date.now();
  room.updatedAt = Date.now();
  settleRoom(room);
  broadcastRoom(room);
}

function handleVote(client, message) {
  const context = requireSession(client, 'vote');
  if (!context) return;
  const { room, player } = context;
  const partner = findPartner(room, player);

  if (room.status !== 'playing' || !room.current || !partner) {
    sendError(client, 'GAME_NOT_ACTIVE', '现在还不能做同义判断。', 'vote');
    return;
  }

  const expectedRound = Number(message.round);
  if (!Number.isInteger(expectedRound) || expectedRound !== room.current.round) {
    sendError(client, 'STALE_ROUND', '这一轮已经翻篇啦，稍等同步。', 'vote');
    return;
  }

  const myWord = room.current.words[player.id] || '';
  const partnerWord = room.current.words[partner.id] || '';
  if (!myWord || !partnerWord || myWord === partnerWord) {
    sendError(client, 'VOTE_NOT_READY', '这一轮已经收好啦。', 'vote');
    return;
  }

  if (room.current.votes[player.id]) {
    sendError(client, 'ALREADY_VOTED', '你已经选过啦。', 'vote');
    return;
  }

  if (message.choice !== 'yes' && message.choice !== 'no') {
    sendError(client, 'INVALID_VOTE', '选「是」或「不是」都可以。', 'vote');
    return;
  }

  room.current.votes[player.id] = message.choice;
  player.lastSeen = Date.now();
  room.updatedAt = Date.now();
  settleRoom(room);
  broadcastRoom(room);
}

function handleRematch(client) {
  const context = requireSession(client, 'rematch');
  if (!context) return;
  const { room, player } = context;

  if (room.status !== 'success') {
    sendError(client, 'NOT_SUCCESS', '这一局还没结束呢。', 'rematch');
    return;
  }

  if (room.players.length !== 2) {
    sendError(client, 'WAITING_PARTNER', '等 TA 也回来，再一起开新局吧。', 'rematch');
    return;
  }

  if (room.rematchVotes[player.id]) {
    sendError(client, 'ALREADY_READY', '已经发起啦，等 TA 也点一下。', 'rematch');
    return;
  }

  room.rematchVotes[player.id] = true;
  player.lastSeen = Date.now();
  room.updatedAt = Date.now();
  settleRematch(room);
  broadcastRoom(room);
}

function handleLeave(client) {
  const context = sessionContext(client);
  if (!context) {
    client.session = null;
    sendJSON(client, { type: 'left' });
    return;
  }

  const { room, player } = context;
  client.session = null;
  deleteRoom(room, 'LEFT', 'TA 离开了房间，房间已经关上啦。', player.id);
  sendJSON(client, { type: 'left' });
}

function handleSync(client) {
  const context = requireSession(client, 'sync');
  if (!context) return;
  const { room, player } = context;
  player.lastSeen = Date.now();
  sendJSON(client, {
    type: 'state',
    room: roomView(room, player)
  });
}

function handleClientClose(client) {
  clients.delete(client);
  const context = sessionContext(client);
  if (!context) return;

  const { room, player } = context;
  if (player.ws === client) {
    player.ws = null;
    player.lastSeen = Date.now();
    room.updatedAt = Date.now();
    broadcastRoom(room);
  }
}

/* ============================================================
   HTTP 静态页面
   ============================================================ */
function setSecurityHeaders(response) {
  response.setHeader('X-Content-Type-Options', 'nosniff');
  response.setHeader('Referrer-Policy', 'no-referrer');
  response.setHeader('Permissions-Policy', 'camera=(), microphone=(), geolocation=()');
  response.setHeader(
    'Content-Security-Policy',
    "default-src 'none'; script-src 'unsafe-inline'; style-src 'unsafe-inline'; connect-src 'self' ws: wss:; img-src data:; base-uri 'none'; form-action 'self'"
  );
}

const server = http.createServer((request, response) => {
  let pathname = '/';
  try {
    pathname = new URL(request.url, 'http://localhost').pathname;
  } catch (error) {
    pathname = '/';
  }

  if (pathname === '/healthz') {
    setSecurityHeaders(response);
    response.writeHead(200, {
      'Content-Type': 'application/json; charset=utf-8',
      'Cache-Control': 'no-store'
    });
    response.end(JSON.stringify({
      ok: true,
      rooms: rooms.size,
      connections: clients.size,
      uptime: Math.round(process.uptime())
    }));
    return;
  }

  if (pathname === '/favicon.ico') {
    response.writeHead(204);
    response.end();
    return;
  }

  if (pathname !== '/' && pathname !== '/index.html') {
    setSecurityHeaders(response);
    response.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
    response.end('Not found');
    return;
  }

  if (request.method !== 'GET' && request.method !== 'HEAD') {
    setSecurityHeaders(response);
    response.writeHead(405, {
      'Content-Type': 'text/plain; charset=utf-8',
      Allow: 'GET, HEAD'
    });
    response.end('Method not allowed');
    return;
  }

  const acceptsGzip = String(request.headers['accept-encoding'] || '').includes('gzip');
  const body = acceptsGzip ? htmlGzip : htmlRaw;

  setSecurityHeaders(response);
  response.writeHead(200, {
    'Content-Type': 'text/html; charset=utf-8',
    'Content-Length': body.length,
    'Cache-Control': 'no-store',
    ...(acceptsGzip ? { 'Content-Encoding': 'gzip', Vary: 'Accept-Encoding' } : {})
  });

  if (request.method === 'HEAD') {
    response.end();
  } else {
    response.end(body);
  }
});

server.on('upgrade', (request, socket, head) => {
  let pathname = '/';
  try {
    pathname = new URL(request.url, 'http://localhost').pathname;
  } catch (error) {
    pathname = '/';
  }

  if (pathname !== '/ws') {
    rejectUpgrade(socket, 404, 'Not found');
    return;
  }

  const upgrade = String(request.headers.upgrade || '').toLowerCase();
  const key = request.headers['sec-websocket-key'];
  const version = request.headers['sec-websocket-version'];

  if (upgrade !== 'websocket' || !key || version !== '13') {
    rejectUpgrade(socket, 400, 'WebSocket handshake failed');
    return;
  }

  const accept = crypto
    .createHash('sha1')
    .update(key + WS_GUID)
    .digest('base64');

  socket.write(
    'HTTP/1.1 101 Switching Protocols\r\n' +
    'Upgrade: websocket\r\n' +
    'Connection: Upgrade\r\n' +
    `Sec-WebSocket-Accept: ${accept}\r\n` +
    '\r\n'
  );

  const client = new WSClient(socket, request, head);
  clients.add(client);
  client.onMessage = handleClientMessage;
  client.onClose = handleClientClose;
});

server.on('clientError', (error, socket) => {
  if (socket.writable) {
    socket.end('HTTP/1.1 400 Bad Request\r\nConnection: close\r\n\r\n');
  }
});

/* ============================================================
   心跳 / 房间清理 / 启动
   ============================================================ */
setInterval(() => {
  for (const client of clients) {
    if (!client.ready) {
      clients.delete(client);
      continue;
    }
    if (!client.isAlive) {
      client.terminate();
      continue;
    }
    client.isAlive = false;
    client.ping();
  }
}, CLIENT_HEARTBEAT_MS).unref();

setInterval(() => {
  const now = Date.now();
  for (const [key, room] of rooms) {
    const hasConnected = room.players.some((player) => Boolean(player.ws));
    const idleFor = now - room.updatedAt;
    const age = now - room.createdAt;
    if ((!hasConnected && idleFor > EMPTY_ROOM_TTL_MS) || age > MAX_ROOM_AGE_MS) {
      rooms.delete(key);
      for (const player of room.players) {
        if (player.ws && player.ws.ready) {
          sendJSON(player.ws, {
            type: 'room-closed',
            code: 'ROOM_EXPIRED',
            message: '这间小屋太久没有动静，先收起来啦。'
          });
          player.ws.session = null;
        }
        player.ws = null;
      }
    }
  }
}, CLEANUP_INTERVAL_MS).unref();

function lanAddresses() {
  const result = [];
  const interfaces = os.networkInterfaces();
  for (const records of Object.values(interfaces)) {
    for (const record of records || []) {
      if (record.family === 'IPv4' && !record.internal) {
        result.push(record.address);
      }
    }
  }
  return result;
}

server.listen(PORT, HOST, () => {
  console.log('');
  console.log('  Same Word · 双人同词相遇（联网版）');
  console.log(`  本机打开： http://localhost:${PORT}`);
  const addresses = lanAddresses();
  if (addresses.length) {
    for (const address of addresses) {
      console.log(`  局域网：   http://${address}:${PORT}`);
    }
  }
  console.log(`  健康检查： http://localhost:${PORT}/healthz`);
  console.log('  按 Ctrl+C 停止服务');
  console.log('');
});

function shutdown() {
  console.log('\n正在关闭房间服务器…');
  for (const client of clients) {
    try {
      sendJSON(client, {
        type: 'server-shutdown',
        message: '服务器正在重启，请稍后重新连接。'
      });
      client.close(1001, 'Server shutting down');
    } catch (error) {
      /* 忽略 */
    }
  }
  server.close(() => process.exit(0));
  setTimeout(() => process.exit(0), 1200).unref();
}

process.on('SIGINT', shutdown);
process.on('SIGTERM', shutdown);

process.on('uncaughtException', (error) => {
  console.error('未捕获异常：', error);
});

process.on('unhandledRejection', (error) => {
  console.error('未处理的 Promise 拒绝：', error);
});
