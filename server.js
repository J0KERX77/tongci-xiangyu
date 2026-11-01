'use strict';
/**
 * 同词相遇 · 联机服务器
 * ------------------------------------------------------------
 * 零依赖，只用 Node 内置模块。
 *   node server.js            默认端口 8790
 *   PORT=8080 node server.js  自定义端口
 *
 * 协议：POST /api/act  { action, ... }  →  JSON
 * 同步：HTTP 长轮询（hold 最多 6 秒），不依赖 WebSocket，
 *       任何浏览器 / 任何代理都能跑通。
 */

const http = require('http');
const fs = require('fs');
const path = require('path');
const os = require('os');
const crypto = require('crypto');

const PORT = Number(process.env.PORT || 8790);
const HOLD_MS = 6000;                 // 长轮询单次最长挂起
const AWAY_MS = 20000;                // 超过多久没有心跳算掉线
const ROOM_TTL = 30 * 60 * 1000;      // 房间空闲多久回收
const MAX_ROUNDS = 20;                // 最多磨多少轮

const ALPHA = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789'; // 去掉了 0O1I 这类易混字符
const rooms = new Map();

/* ============================================================
 * 基础工具
 * ========================================================== */
function nowMs() { return Date.now(); }

function newCode() {
  for (let i = 0; i < 500; i++) {
    let c = '';
    for (let j = 0; j < 4; j++) c += ALPHA[Math.floor(Math.random() * ALPHA.length)];
    if (!rooms.has(c)) return c;
  }
  return null;
}

function newToken() { return crypto.randomBytes(9).toString('hex'); }

function cleanName(n) {
  const s = String(n == null ? '' : n).replace(/[\r\n\t]/g, ' ').trim().slice(0, 8);
  return s || '玩家';
}

/* 词归一化：全角转半角 → 去空格/标点/符号（含 emoji）→ 小写 */
function fold(s) {
  const t = String(s == null ? '' : s)
    .replace(/[\uFF01-\uFF5E]/g, (c) => String.fromCharCode(c.charCodeAt(0) - 0xFEE0))
    .replace(/\u3000/g, ' ')
    .toLowerCase();
  try { return t.replace(/[\s\p{P}\p{S}]/gu, ''); }
  catch (e) { return t.replace(/[\s!-\/:-@\[-`{-~]/g, ''); }
}

function send(res, code, obj) {
  try {
    if (!res || res.writableEnded || res.destroyed) return;
    const body = JSON.stringify(obj);
    res.writeHead(code, {
      'Content-Type': 'application/json; charset=utf-8',
      'Cache-Control': 'no-store',
      'Content-Length': Buffer.byteLength(body)
    });
    res.end(body);
  } catch (e) {
    try { res.destroy(); } catch (e2) { /* ignore */ }
  }
}

/* ============================================================
 * 房间模型
 * ========================================================== */
function newPlayer(name) {
  return {
    name: name,
    token: newToken(),
    ready: false,
    word: '',
    submitted: false,
    lastSeen: nowMs()
  };
}

function makeRoom(hostName, limit) {
  const code = newCode();
  if (!code) return null;
  const room = {
    code: code,
    v: 1,
    createdAt: nowMs(),
    phase: 'lobby',            // lobby | play | reveal | win | over
    round: 0,
    timeLimit: (limit === 0 || limit === 30 || limit === 60) ? limit : 60,
    history: [],
    deadline: 0,
    paused: false,
    pausedAt: 0,
    over: null,
    acks: { p1: false, p2: false },
    host: 'p1',
    players: { p1: newPlayer(hostName), p2: null },
    waiters: new Set()
  };
  rooms.set(code, room);
  return room;
}

/* 只发当前玩家该看到的东西：对局中绝不泄露对方的词 */
function pub(room, me) {
  const P = room.players;
  const other = me === 'p1' ? 'p2' : 'p1';
  const hideOther = (room.phase === 'play' || room.phase === 'lobby');
  const t = nowMs();
  return {
    code: room.code,
    you: me,
    phase: room.phase,
    round: room.round,
    timeLimit: room.timeLimit,
    deadline: room.deadline,
    paused: room.paused,
    host: room.host,
    names: { p1: P.p1 ? P.p1.name : '', p2: P.p2 ? P.p2.name : '' },
    ready: { p1: !!(P.p1 && P.p1.ready), p2: !!(P.p2 && P.p2.ready) },
    submitted: { p1: !!(P.p1 && P.p1.submitted), p2: !!(P.p2 && P.p2.submitted) },
    present: {
      p1: !!(P.p1 && t - P.p1.lastSeen < AWAY_MS),
      p2: !!(P.p2 && t - P.p2.lastSeen < AWAY_MS)
    },
    youWord: P[me] ? String(P[me].word || '') : '',
    otherWord: (hideOther || !P[other]) ? '' : String(P[other].word || ''),
    acks: { p1: !!room.acks.p1, p2: !!room.acks.p2 },
    history: room.history.map((h) => ({
      a: h.a, b: h.b, hit: !!h.hit, timeout: !!h.timeout
    })),
    over: room.over,
    now: t
  };
}

/* 广播：版本号 +1，唤醒所有挂着等的人 */
function bump(room) {
  room.v += 1;
  if (!room.waiters || room.waiters.size === 0) return;
  const list = Array.from(room.waiters);
  room.waiters.clear();
  for (const w of list) {
    clearTimeout(w.timer);
    if (rooms.has(room.code) && room.players[w.pid]) {
      send(w.res, 200, { v: room.v, now: nowMs(), state: pub(room, w.pid) });
    } else {
      send(w.res, 200, { error: 'no_room' });
    }
  }
}

function respondState(room, pid, res) {
  send(res, 200, { v: room.v, now: nowMs(), state: pub(room, pid) });
}

/* ============================================================
 * 对局状态机
 * ========================================================== */
function startRound(room) {
  room.round += 1;
  room.phase = 'play';
  room.over = null;
  room.acks = { p1: false, p2: false };
  room.paused = false;
  room.pausedAt = 0;
  room.deadline = room.timeLimit ? nowMs() + room.timeLimit * 1000 : 0;
  ['p1', 'p2'].forEach((k) => {
    if (room.players[k]) { room.players[k].word = ''; room.players[k].submitted = false; }
  });
}

function finishRound(room) {
  const P = room.players;
  const a = P.p1 ? P.p1.word : '';
  const b = P.p2 ? P.p2.word : '';
  const fa = fold(a);
  const hit = !!fa && fa === fold(b);
  room.history.push({ a: a, b: b, hit: hit, timeout: false });
  room.phase = hit ? 'win' : 'reveal';
  room.deadline = 0;
  room.paused = false;
  room.pausedAt = 0;
  room.acks = { p1: false, p2: false };
  if (hit) room.winRound = room.round;
}

function timeUp(room) {
  const P = room.players;
  const names = ['p1', 'p2']
    .filter((k) => P[k] && !P[k].submitted)
    .map((k) => P[k].name);
  room.history.push({
    a: P.p1 ? (P.p1.word || '') : '',
    b: P.p2 ? (P.p2.word || '') : '',
    hit: false,
    timeout: true
  });
  room.phase = 'over';
  room.deadline = 0;
  room.paused = false;
  room.over = {
    reason: 'timeout',
    text: (names.length ? names.join(' 和 ') : '有人') + ' 没能在 ' + room.timeLimit + ' 秒内想到词'
  };
}

/* 每次有人来都跑一遍：掉线暂停 / 到点判负 */
function tick(room) {
  if (room.phase !== 'play' || !room.deadline) return;
  const t = nowMs();
  const away = ['p1', 'p2'].some((k) => room.players[k] && t - room.players[k].lastSeen > AWAY_MS);

  if (away && !room.paused) {
    room.paused = true;
    room.pausedAt = t;
    bump(room);
    return;
  }
  if (!away && room.paused) {
    room.deadline += (t - room.pausedAt);
    room.paused = false;
    room.pausedAt = 0;
    bump(room);
  }
  if (!room.paused && t >= room.deadline) {
    timeUp(room);
    bump(room);
  }
}

/* ============================================================
 * 动作
 * ========================================================== */
function auth(msg) {
  const pid = msg.pid;
  if (pid !== 'p1' && pid !== 'p2') return null;
  const room = rooms.get(String(msg.code || '').toUpperCase());
  if (!room) return null;
  const p = room.players[pid];
  if (!p || p.token !== msg.token) return null;
  return { room: room, pid: pid };
}

function doCreate(msg, res) {
  const room = makeRoom(cleanName(msg.name), Number(msg.limit));
  if (!room) return send(res, 200, { error: 'busy' });
  bump(room);
  send(res, 200, {
    ok: 1, v: room.v, now: nowMs(),
    code: room.code, pid: 'p1', token: room.players.p1.token,
    state: pub(room, 'p1')
  });
}

function doJoin(msg, res) {
  const code = String(msg.code || '').trim().toUpperCase();
  const room = rooms.get(code);
  if (!room) return send(res, 200, { error: 'no_room' });
  if (room.phase !== 'lobby') return send(res, 200, { error: 'started' });
  if (room.players.p2) return send(res, 200, { error: 'full' });

  room.players.p2 = newPlayer(cleanName(msg.name));
  room.players.p1 && (room.players.p1.ready = false);
  bump(room);
  send(res, 200, {
    ok: 1, v: room.v, now: nowMs(),
    code: room.code, pid: 'p2', token: room.players.p2.token,
    state: pub(room, 'p2')
  });
}

function doState(msg, res) {
  const a = auth(msg);
  if (!a) return send(res, 200, { error: 'no_room' });
  const room = a.room;
  const pid = a.pid;

  room.players[pid].lastSeen = nowMs();
  tick(room);

  const since = Number(msg.v) || 0;
  if (room.v > since) return respondState(room, pid, res);
  hold(room, pid, res);
}

/* 长轮询：有变化立刻回，没变化挂一会儿 */
function hold(room, pid, res) {
  const w = { pid: pid, res: res, timer: null };
  room.waiters.add(w);

  let ms = HOLD_MS;
  if (room.phase === 'play' && room.deadline && !room.paused) {
    ms = Math.min(ms, Math.max(80, room.deadline - nowMs()));
  }

  w.timer = setTimeout(() => {
    room.waiters.delete(w);
    if (!rooms.has(room.code) || !room.players[pid]) {
      return send(res, 200, { error: 'no_room' });
    }
    room.players[pid].lastSeen = nowMs();
    tick(room);                       // 可能正好到点
    respondState(room, pid, res);
  }, ms);

  res.on('close', () => {
    clearTimeout(w.timer);
    room.waiters.delete(w);
  });
}

function doReady(msg, res) {
  const a = auth(msg);
  if (!a) return send(res, 200, { error: 'no_room' });
  const room = a.room, pid = a.pid;
  room.players[pid].lastSeen = nowMs();

  if (room.phase === 'lobby') {
    room.players[pid].ready = !!msg.ready;
    const P = room.players;
    if (P.p1 && P.p2 && P.p1.ready && P.p2.ready) {
      room.history = [];
      startRound(room);
    }
  }
  bump(room);
  send(res, 200, { ok: 1, v: room.v, now: nowMs(), state: pub(room, pid) });
}

function doLimit(msg, res) {
  const a = auth(msg);
  if (!a) return send(res, 200, { error: 'no_room' });
  const room = a.room, pid = a.pid;
  room.players[pid].lastSeen = nowMs();
  if (room.phase === 'lobby' && room.host === pid) {
    const v = Number(msg.limit);
    room.timeLimit = (v === 0 || v === 30 || v === 60) ? v : room.timeLimit;
    bump(room);
  }
  send(res, 200, { ok: 1, v: room.v, now: nowMs(), state: pub(room, pid) });
}

function doSubmit(msg, res) {
  const a = auth(msg);
  if (!a) return send(res, 200, { error: 'no_room' });
  const room = a.room, pid = a.pid;
  const me = room.players[pid];
  me.lastSeen = nowMs();

  if (room.phase !== 'play') return send(res, 200, { error: 'bad_phase' });
  if (me.submitted) return send(res, 200, { error: 'already' });

  const word = String(msg.word == null ? '' : msg.word).replace(/\s+/g, ' ').trim().slice(0, 12);
  if (!fold(word)) return send(res, 200, { error: 'empty' });

  me.word = word;
  me.submitted = true;

  const P = room.players;
  if (P.p1 && P.p1.submitted && P.p2 && P.p2.submitted) finishRound(room);
  bump(room);
  send(res, 200, { ok: 1, v: room.v, now: nowMs(), state: pub(room, pid) });
}

function doAck(msg, res) {
  const a = auth(msg);
  if (!a) return send(res, 200, { error: 'no_room' });
  const room = a.room, pid = a.pid;
  room.players[pid].lastSeen = nowMs();

  if (room.phase === 'reveal' && !room.acks[pid]) {
    room.acks[pid] = true;
    const P = room.players;
    if (P.p1 && P.p2 && room.acks.p1 && room.acks.p2) {
      if (room.round >= MAX_ROUNDS) {
        room.phase = 'over';
        room.over = { reason: 'long', text: '已经磨了 ' + room.round + ' 轮还没撞上，缘分藏得有点深' };
      } else {
        startRound(room);
      }
    }
    bump(room);
  }
  send(res, 200, { ok: 1, v: room.v, now: nowMs(), state: pub(room, pid) });
}

function doRestart(msg, res) {
  const a = auth(msg);
  if (!a) return send(res, 200, { error: 'no_room' });
  const room = a.room, pid = a.pid;
  room.players[pid].lastSeen = nowMs();

  room.phase = 'lobby';
  room.round = 0;
  room.history = [];
  room.over = null;
  room.deadline = 0;
  room.paused = false;
  room.acks = { p1: false, p2: false };
  ['p1', 'p2'].forEach((k) => {
    const p = room.players[k];
    if (p) { p.ready = false; p.word = ''; p.submitted = false; }
  });
  bump(room);
  send(res, 200, { ok: 1, v: room.v, now: nowMs(), state: pub(room, pid) });
}

function doLeave(msg, res) {
  const a = auth(msg);
  if (!a) return send(res, 200, { ok: 1 });
  const room = a.room, pid = a.pid;

  room.players[pid] = null;

  if (!room.players.p1 && !room.players.p2) {
    const list = Array.from(room.waiters);
    room.waiters.clear();
    for (const w of list) { clearTimeout(w.timer); send(w.res, 200, { error: 'no_room' }); }
    rooms.delete(room.code);
    return send(res, 200, { ok: 1 });
  }

  if (pid === room.host) room.host = room.players.p1 ? 'p1' : 'p2';

  // 中途退出就退回大厅，等对方再准备
  room.phase = 'lobby';
  room.round = 0;
  room.history = [];
  room.over = null;
  room.deadline = 0;
  room.paused = false;
  room.acks = { p1: false, p2: false };
  ['p1', 'p2'].forEach((k) => { if (room.players[k]) room.players[k].ready = false; });

  bump(room);
  send(res, 200, { ok: 1 });
}

/* ============================================================
 * HTTP
 * ========================================================== */
function handleApi(msg, res) {
  if (!msg || typeof msg !== 'object') return send(res, 200, { error: 'bad_req' });
  switch (String(msg.action || '')) {
    case 'create': return doCreate(msg, res);
    case 'join': return doJoin(msg, res);
    case 'state': return doState(msg, res);
    case 'ready': return doReady(msg, res);
    case 'limit': return doLimit(msg, res);
    case 'submit': return doSubmit(msg, res);
    case 'ack': return doAck(msg, res);
    case 'restart': return doRestart(msg, res);
    case 'leave': return doLeave(msg, res);
    default: return send(res, 200, { error: 'bad_action' });
  }
}

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.svg': 'image/svg+xml',
  '.ico': 'image/x-icon',
  '.txt': 'text/plain; charset=utf-8'
};

const server = http.createServer((req, res) => {
  let u;
  try {
    u = new URL(req.url, 'http://' + (req.headers.host || 'localhost'));
  } catch (e) {
    return send(res, 400, { error: 'bad_url' });
  }

  if (u.pathname === '/api/act') {
    if (req.method !== 'POST') return send(res, 405, { error: 'method' });
    const chunks = [];
    let size = 0;
    let bad = false;
    req.on('data', (c) => {
      size += c.length;
      if (size > 32000) { bad = true; req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => {
      if (bad) return;
      let msg;
      try { msg = JSON.parse(Buffer.concat(chunks).toString('utf8') || '{}'); }
      catch (e) { return send(res, 200, { error: 'bad_json' }); }
      try { handleApi(msg, res); }
      catch (e) { console.error('[api]', e); send(res, 200, { error: 'server' }); }
    });
    return;
  }

  if (u.pathname === '/healthz') {
    return send(res, 200, { ok: 1, rooms: rooms.size, uptime: Math.round(process.uptime()) });
  }

  // 静态文件
  let rel;
  try { rel = decodeURIComponent(u.pathname); }
  catch (e) { rel = '/'; }
  if (rel === '/' || rel === '') rel = '/index.html';
  const file = path.join(__dirname, rel);
  if (file.indexOf(__dirname) !== 0) {
    res.writeHead(403, { 'Content-Type': 'text/plain; charset=utf-8' });
    return res.end('403');
  }
  fs.readFile(file, (err, data) => {
    if (err) {
      res.writeHead(404, { 'Content-Type': 'text/plain; charset=utf-8' });
      return res.end('404 Not Found');
    }
    res.writeHead(200, {
      'Content-Type': MIME[path.extname(file).toLowerCase()] || 'application/octet-stream',
      'Cache-Control': 'no-cache'
    });
    res.end(data);
  });
});

server.on('clientError', (err, socket) => {
  try { socket.destroy(); } catch (e) { /* ignore */ }
});

/* 空闲房间回收 */
setInterval(() => {
  const t = nowMs();
  for (const [code, room] of rooms) {
    let last = 0;
    ['p1', 'p2'].forEach((k) => {
      if (room.players[k]) last = Math.max(last, room.players[k].lastSeen);
    });
    if (t - last > ROOM_TTL) {
      const list = Array.from(room.waiters);
      room.waiters.clear();
      for (const w of list) { clearTimeout(w.timer); send(w.res, 200, { error: 'no_room' }); }
      rooms.delete(code);
    }
  }
}, 60000).unref();

function lanIPs() {
  const out = [];
  const nets = os.networkInterfaces();
  Object.keys(nets).forEach((k) => {
    (nets[k] || []).forEach((n) => {
      const fam = n.family;
      if ((fam === 'IPv4' || fam === 4) && !n.internal) out.push(n.address);
    });
  });
  return out;
}

server.listen(PORT, '0.0.0.0', () => {
  const ips = lanIPs();
  console.log('');
  console.log('  ┌────────────────────────────────────────────────┐');
  console.log('  │   同词相遇 · 联机服务器已启动                  │');
  console.log('  └────────────────────────────────────────────────┘');
  console.log('');
  console.log('  本机打开   http://localhost:' + PORT + '/');
  if (ips.length) {
    ips.forEach((ip) => console.log('  手机打开   http://' + ip + ':' + PORT + '/   （同一 WiFi）'));
  } else {
    console.log('  手机打开   没检测到局域网 IP，请检查网络连接');
  }
  console.log('');
  console.log('  异地的朋友也要玩？把这个端口映射出去再发网址：');
  console.log('      cloudflared tunnel --url http://localhost:' + PORT);
  console.log('      或  ngrok http ' + PORT);
  console.log('');
  console.log('  Ctrl + C 停止服务');
  console.log('');
});

server.on('error', (e) => {
  if (e && e.code === 'EADDRINUSE') {
    console.error('');
    console.error('  端口 ' + PORT + ' 被占用了。换个端口再来：');
    console.error('      set PORT=8791 && node server.js');
    console.error('');
  } else {
    console.error('[server]', e);
  }
  process.exit(1);
});

process.on('uncaughtException', (e) => {
  console.error('[uncaught]', e && e.stack ? e.stack : e);
});
