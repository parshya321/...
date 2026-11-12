'use strict';
/**
 * Anime Mini App API
 *
 * - Sirf Telegram Mini App ke andar se chalta hai (initData signature check).
 * - Saari live titles memory mein rehti hain: home / list / search turant.
 * - Video link kabhi seedha nahi: /api/play ek chhota token deta hai, player /p/<token> pe khulta hai.
 * - Har user ki limit, zyada tezi pe auto-ban + admin bot pe alert.
 * - Adult titles: home/list mein nahi, search mein normal; kholne pe 18+ popup (age_required).
 *
 * Ye API database mein sirf "users" collection mein likhta hai. titles/episodes sirf padhta hai.
 */
try { require('dotenv').config(); } catch (e) { /* optional */ }

const http = require('http');
const crypto = require('crypto');
const zlib = require('zlib');
const fs = require('fs');
const path = require('path');

/* ------------------------------------------------------------------ */
/* Config                                                              */
/* ------------------------------------------------------------------ */
const env = process.env;
const CFG = {
  port: +env.PORT || 3000,
  mongo: env.MONGO_URI,
  dbName: env.DB_NAME || 'animedb',
  botToken: env.BOT_TOKEN || '',              // PUBLIC bot (users wala)
  publicUrl: (env.PUBLIC_URL || '').replace(/\/+$/, ''), // is service ka https address
  miniAppUrl: (env.MINIAPP_URL || '').replace(/\/+$/, ''), // Mini App ka address (khaali = PUBLIC_URL)
  adminBot: env.ADMIN_BOT_TOKEN || '',        // scraper wala bot (sirf alert bhejne ke liye)
  adminChat: env.ADMIN_CHAT_ID || '',
  adultGenres: (env.ADULT_GENRES || 'Hentai,Erotica,Adult').split(',').map((s) => s.trim().toLowerCase()).filter(Boolean),
  initDataMaxAge: +env.INITDATA_MAX_AGE || 24 * 3600,
  tokenTtl: +env.PLAY_TOKEN_SECONDS || 300,
  refreshSec: +env.REFRESH_SECONDS || 120,
  pageSize: 30,
  lim: {
    apiPerMin: +env.LIMIT_API_PER_MIN || 120,
    playPer5Min: +env.LIMIT_PLAY_PER_5MIN || 30,
    playPerDay: +env.LIMIT_PLAY_PER_DAY || 300,
    ipPerMin: +env.LIMIT_IP_PER_MIN || 240,
    banPlayAttempts5Min: +env.BAN_PLAY_ATTEMPTS_5MIN || 80,
    banBlockedPerMin: +env.BAN_BLOCKED_PER_MIN || 300,
  },
};
CFG.webhookSecret = CFG.botToken ? crypto.createHash('sha256').update('wh:' + CFG.botToken).digest('hex').slice(0, 32) : '';

const log = (...a) => console.log(new Date().toISOString().slice(11, 19), ...a);

/* ------------------------------------------------------------------ */
/* Telegram initData check                                             */
/* https://core.telegram.org/bots/webapps#validating-data-received-via-the-mini-app */
/* ------------------------------------------------------------------ */
function checkInitData(initData, botToken, maxAgeSec, nowSec) {
  if (!initData || !botToken) return null;
  let params;
  try { params = new URLSearchParams(initData); } catch (e) { return null; }
  const hash = params.get('hash');
  if (!hash || !/^[0-9a-f]{64}$/i.test(hash)) return null;
  const secret = crypto.createHmac('sha256', 'WebAppData').update(botToken).digest();
  const make = (skip) => {
    const pairs = [];
    for (const [k, v] of params) if (!skip.includes(k)) pairs.push(`${k}=${v}`);
    pairs.sort();
    return crypto.createHmac('sha256', secret).update(pairs.join('\n')).digest();
  };
  const given = Buffer.from(hash, 'hex');
  // naye Telegram versions mein "signature" field bhi aata hai; dono tarah check karo
  const ok = [['hash'], ['hash', 'signature']].some((skip) => {
    const calc = make(skip);
    return calc.length === given.length && crypto.timingSafeEqual(calc, given);
  });
  if (!ok) return null;
  const authDate = +params.get('auth_date') || 0;
  const now = nowSec || Math.floor(Date.now() / 1000);
  if (!authDate || now - authDate > maxAgeSec || authDate - now > 300) return null;
  let user;
  try { user = JSON.parse(params.get('user') || 'null'); } catch (e) { return null; }
  if (!user || !user.id) return null;
  return { user, authDate };
}

/* ------------------------------------------------------------------ */
/* Rate limiter (memory)                                               */
/* ------------------------------------------------------------------ */
class Window {
  constructor(ms) { this.ms = ms; this.map = new Map(); }
  hit(key, n = 1) {
    const now = Date.now();
    let e = this.map.get(key);
    if (!e || now >= e.reset) { e = { count: 0, reset: now + this.ms }; this.map.set(key, e); }
    e.count += n;
    return e;
  }
  peek(key) {
    const e = this.map.get(key);
    return e && Date.now() < e.reset ? e.count : 0;
  }
  sweep() { const now = Date.now(); for (const [k, e] of this.map) if (now >= e.reset) this.map.delete(k); }
}
const W = {
  api: new Window(60e3), ip: new Window(60e3), blocked: new Window(60e3),
  play5: new Window(5 * 60e3), playAttempt5: new Window(5 * 60e3), playDay: new Window(24 * 3600e3),
};

/* ------------------------------------------------------------------ */
/* Text helpers                                                        */
/* ------------------------------------------------------------------ */
function norm(s) {
  return String(s || '').toLowerCase().normalize('NFKD').replace(/[̀-ͯ]/g, '')
    .replace(/&/g, ' and ').replace(/[^a-z0-9ऀ-ॿ]+/g, ' ').trim();
}
const squash = (s) => s.replace(/\s+/g, '');

/* ------------------------------------------------------------------ */
/* Catalog store (memory)                                              */
/* ------------------------------------------------------------------ */
const store = {
  list: [], byKey: new Map(), home: null, homeGz: null, homeEtag: '', meta: null, loadedAt: 0, version: '',
};

function isAdult(doc) {
  if (doc.adult === true) return true;
  if (doc.adult === false) return false;
  return (doc.genres || []).some((g) => CFG.adultGenres.includes(String(g).toLowerCase()));
}

function card(t) {
  return { type: t.type, slug: t.slug, title: t.title, poster: t.poster || null, year: t.year || null, adult: t.adult || undefined,
    eps: t.type === 'series' ? t.episodes || undefined : undefined };
}

function buildStore(docs) {
  const list = [];
  const byKey = new Map();
  for (const d of docs) {
    if (!d.title || !d.slug) continue;
    const t = {
      key: `${d.type}:${d.slug}`, type: d.type, slug: d.slug, title: d.title,
      overview: d.overview || '', genres: d.genres || [], languages: d.languages || [],
      year: d.year || null, runtime: d.runtime || null, poster: d.poster || null, backdrop: d.backdrop || null,
      seasons: (d.seasons || []).map((s) => ({ season: s.season, from: s.from, to: s.to, count: s.count, sub: !!s.sub })),
      episodes: d.episodes_listed || null, no_episodes: !!d.no_episodes,
      updated: d.lastmod_site ? Date.parse(d.lastmod_site) || 0 : 0,
      adult: isAdult(d),
    };
    t.n = norm(t.title);
    t.ns = squash(t.n);
    list.push(t);
    byKey.set(t.key, t);
  }
  list.sort((a, b) => b.updated - a.updated || a.title.localeCompare(b.title));

  const safe = list.filter((t) => !t.adult);
  const count = (field) => {
    const m = new Map();
    for (const t of safe) for (const g of t[field]) m.set(g, (m.get(g) || 0) + 1);
    return [...m.entries()].sort((a, b) => b[1] - a[1]).map(([name, n]) => ({ name, n }));
  };
  const genres = count('genres');
  const languages = count('languages');
  const rows = genres.slice(0, 8).map((g) => ({
    title: g.name, genre: g.name,
    items: safe.filter((t) => t.genres.includes(g.name)).slice(0, 15).map(card),
  }));
  const home = {
    latest: safe.slice(0, 20).map(card),
    series: safe.filter((t) => t.type === 'series').slice(0, 20).map(card),
    movies: safe.filter((t) => t.type === 'movie').slice(0, 20).map(card),
    rows,
    genres, languages,
    total: { series: safe.filter((t) => t.type === 'series').length, movies: safe.filter((t) => t.type === 'movie').length },
  };
  const body = Buffer.from(JSON.stringify(home));
  return {
    list, byKey, home, homeBody: body, homeGz: zlib.gzipSync(body),
    homeEtag: '"h' + crypto.createHash('sha1').update(body).digest('hex').slice(0, 16) + '"',
    meta: { genres, languages }, loadedAt: Date.now(),
  };
}

function search(q, { includeAdult, page }) {
  const nq = norm(q);
  if (!nq) return { items: [], total: 0 };
  const words = nq.split(' ');
  const sq = squash(nq);
  const hits = [];
  for (const t of store.list) {
    if (t.adult && !includeAdult) continue;
    let s = 0;
    if (t.n === nq) s = 100;
    else if (t.n.startsWith(nq)) s = 80;
    else if ((' ' + t.n).includes(' ' + nq)) s = 65;
    else if (t.n.includes(nq)) s = 50;
    else if (words.every((w) => t.n.includes(w))) s = 40;
    else if (sq.length >= 3 && t.ns.includes(sq)) s = 30;
    if (s) hits.push([s, t]);
  }
  hits.sort((a, b) => b[0] - a[0] || b[1].updated - a[1].updated);
  const p = Math.max(1, page || 1);
  return {
    total: hits.length,
    items: hits.slice((p - 1) * CFG.pageSize, p * CFG.pageSize).map((h) => card(h[1])),
    more: hits.length > p * CFG.pageSize,
  };
}

function listTitles({ type, genre, lang, sort, page }) {
  let arr = store.list.filter((t) => !t.adult);
  if (type === 'series' || type === 'movie') arr = arr.filter((t) => t.type === type);
  if (genre) { const g = genre.toLowerCase(); arr = arr.filter((t) => t.genres.some((x) => x.toLowerCase() === g)); }
  if (lang) { const l = lang.toLowerCase(); arr = arr.filter((t) => t.languages.some((x) => x.toLowerCase() === l)); }
  if (sort === 'az') arr = [...arr].sort((a, b) => a.title.localeCompare(b.title));
  else if (sort === 'year') arr = [...arr].sort((a, b) => (+b.year || 0) - (+a.year || 0));
  const p = Math.max(1, page || 1);
  return {
    total: arr.length,
    items: arr.slice((p - 1) * CFG.pageSize, p * CFG.pageSize).map(card),
    more: arr.length > p * CFG.pageSize,
  };
}

/* ------------------------------------------------------------------ */
/* Users                                                               */
/* ------------------------------------------------------------------ */
const users = new Map(); // id -> { age, banned, seenWrite }
const banned = new Set();

async function getUser(db, tgUser) {
  const id = String(tgUser.id);
  let u = users.get(id);
  if (!u) {
    const doc = await db.collection('users').findOne({ _id: id });
    u = { age: doc ? doc.age || null : null, banned: !!(doc && doc.banned), seenWrite: 0 };
    users.set(id, u);
    if (u.banned) banned.add(id);
  }
  if (Date.now() - u.seenWrite > 5 * 60e3) {
    u.seenWrite = Date.now();
    db.collection('users').updateOne({ _id: id }, {
      $set: { first_name: tgUser.first_name || '', username: tgUser.username || '', lang: tgUser.language_code || '', last_seen: new Date() },
      $setOnInsert: { created_at: new Date(), age: null, banned: false },
    }, { upsert: true }).catch((e) => log('user save fail', e.message));
  }
  return u;
}

async function banUser(db, id, reason) {
  if (banned.has(id)) return;
  banned.add(id);
  const u = users.get(id); if (u) u.banned = true;
  await db.collection('users').updateOne({ _id: id }, { $set: { banned: true, ban_reason: reason, banned_at: new Date() } }, { upsert: true }).catch(() => {});
  log('AUTO-BAN', id, reason);
  adminAlert(`🚫 Auto-ban: user ${id}\nWajah: ${reason}`);
}

/* ------------------------------------------------------------------ */
/* Telegram calls                                                      */
/* ------------------------------------------------------------------ */
async function tg(token, method, payload) {
  if (!token) return null;
  try {
    const r = await fetch(`https://api.telegram.org/bot${token}/${method}`, {
      method: 'POST', headers: { 'content-type': 'application/json' }, body: JSON.stringify(payload || {}),
    });
    return await r.json();
  } catch (e) { log('telegram', method, e.message); return null; }
}
let lastAlerts = [];
function adminAlert(text) {
  if (!CFG.adminBot || !CFG.adminChat) return;
  const now = Date.now();
  lastAlerts = lastAlerts.filter((t) => now - t < 60e3);
  if (lastAlerts.length >= 10) return; // spam mat karo
  lastAlerts.push(now);
  tg(CFG.adminBot, 'sendMessage', { chat_id: CFG.adminChat, text: '[API] ' + text }).catch(() => {});
}

/* ------------------------------------------------------------------ */
/* Play tokens + player page                                           */
/* ------------------------------------------------------------------ */
const tokens = new Map(); // token -> { u, src: [url], exp }

function serverOptions(servers) {
  const list = (servers || []).filter((s) => s && s.url && /^https:\/\//.test(s.url));
  list.sort((a, b) => (a.order || 0) - (b.order || 0));
  return list.map((s, n) => ({ n, name: s.server || `Server ${n + 1}`, lang: s.lang || null, url: s.url }));
}

function makeToken(userId, opts) {
  const t = crypto.randomBytes(18).toString('base64url');
  tokens.set(t, { u: userId, src: opts.map((o) => o.url), exp: Date.now() + CFG.tokenTtl * 1000 });
  return t;
}

const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));

function playerHtml(src) {
  return `<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="referrer" content="no-referrer"><title>Player</title>
<style>html,body{margin:0;height:100%;background:#000;overflow:hidden}iframe{position:fixed;inset:0;width:100%;height:100%;border:0}</style>
</head><body oncontextmenu="return false">
<iframe src="${esc(src)}" sandbox="allow-scripts allow-same-origin allow-presentation" referrerpolicy="no-referrer"
 allow="autoplay; fullscreen; encrypted-media; picture-in-picture" allowfullscreen></iframe>
</body></html>`;
}

/* ------------------------------------------------------------------ */
/* HTTP helpers                                                        */
/* ------------------------------------------------------------------ */
const SEC_HEADERS = {
  'x-content-type-options': 'nosniff',
  'referrer-policy': 'no-referrer',
};

function send(req, res, status, body, headers) {
  const h = Object.assign({}, SEC_HEADERS, headers || {});
  let buf = Buffer.isBuffer(body) ? body : Buffer.from(body);
  if (buf.length > 1024 && /\bgzip\b/.test(req.headers['accept-encoding'] || '') && !h['content-encoding']) {
    buf = zlib.gzipSync(buf); h['content-encoding'] = 'gzip'; h.vary = 'Accept-Encoding';
  }
  h['content-length'] = buf.length;
  res.writeHead(status, h);
  res.end(req.method === 'HEAD' ? undefined : buf);
}
function json(req, res, status, obj, cache) {
  send(req, res, status, JSON.stringify(obj), {
    'content-type': 'application/json; charset=utf-8',
    'cache-control': cache ? `private, max-age=${cache}` : 'no-store',
  });
}
const fail = (req, res, status, error, extra) => json(req, res, status, Object.assign({ error }, extra || {}));

function readBody(req, limit = 64 * 1024) {
  return new Promise((resolve, reject) => {
    let size = 0; const chunks = [];
    req.on('data', (c) => { size += c.length; if (size > limit) { reject(new Error('too_large')); req.destroy(); } else chunks.push(c); });
    req.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
    req.on('error', reject);
  });
}
async function readJson(req) {
  const s = await readBody(req);
  if (!s) return {};
  try { return JSON.parse(s); } catch (e) { return {}; }
}
function clientIp(req) {
  const xf = String(req.headers['x-forwarded-for'] || '').split(',')[0].trim();
  return xf || req.socket.remoteAddress || '?';
}

/* ------------------------------------------------------------------ */
/* Static Mini App files (./public)                                    */
/* ------------------------------------------------------------------ */
const PUBLIC_DIR = path.join(__dirname, 'public');
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8',
  '.svg': 'image/svg+xml', '.png': 'image/png', '.jpg': 'image/jpeg', '.webp': 'image/webp', '.ico': 'image/x-icon', '.json': 'application/json' };
const staticCache = new Map();
function serveStatic(req, res, pathname) {
  let rel = decodeURIComponent(pathname).replace(/^\/+/, '');
  if (!rel || !path.extname(rel)) rel = 'index.html';
  const file = path.normalize(path.join(PUBLIC_DIR, rel));
  if (!file.startsWith(PUBLIC_DIR)) return fail(req, res, 400, 'bad_path');
  let hit = staticCache.get(file);
  if (!hit) {
    if (!fs.existsSync(file)) {
      if (rel !== 'index.html') return fail(req, res, 404, 'not_found');
      return send(req, res, 200, 'API chal raha hai. Mini App abhi upload nahi hua.', { 'content-type': 'text/plain; charset=utf-8' });
    }
    hit = { body: fs.readFileSync(file), type: MIME[path.extname(file)] || 'application/octet-stream' };
    staticCache.set(file, hit);
  }
  send(req, res, 200, hit.body, {
    'content-type': hit.type,
    'cache-control': rel === 'index.html' ? 'no-cache' : 'public, max-age=86400',
  });
}

/* ------------------------------------------------------------------ */
/* Routes                                                              */
/* ------------------------------------------------------------------ */
function createHandler(db) {
  async function authed(req, res) {
    const h = String(req.headers.authorization || '');
    const initData = h.startsWith('tma ') ? h.slice(4) : String(req.headers['x-init-data'] || '');
    const auth = checkInitData(initData, CFG.botToken, CFG.initDataMaxAge);
    if (!auth) { fail(req, res, 401, 'telegram_only'); return null; }
    const id = String(auth.user.id);
    if (banned.has(id)) { fail(req, res, 403, 'banned'); return null; }
    const a = W.api.hit(id);
    if (a.count > CFG.lim.apiPerMin) {
      const b = W.blocked.hit(id);
      if (b.count > CFG.lim.banBlockedPerMin) await banUser(db, id, `1 minute mein ${a.count}+ requests`);
      fail(req, res, 429, 'slow_down', { retry: Math.ceil((a.reset - Date.now()) / 1000) });
      return null;
    }
    const u = await getUser(db, auth.user);
    if (u.banned) { banned.add(id); fail(req, res, 403, 'banned'); return null; }
    return { id, user: auth.user, u };
  }

  // adult title kholne ke liye 18+ chahiye
  function ageGate(req, res, t, ctx) {
    if (!t.adult) return true;
    if (ctx.u.age === 'adult') return true;
    fail(req, res, 403, ctx.u.age === 'minor' ? 'age_blocked' : 'age_required');
    return false;
  }

  const epCache = new Map(); // `${slug}:${season}` -> { at, items }

  async function seasonEpisodes(slug, season) {
    const k = `${slug}:${season}`;
    const c = epCache.get(k);
    if (c && Date.now() - c.at < CFG.refreshSec * 1000) return c.items;
    const rows = await db.collection('episodes').aggregate([
      { $match: { series_slug: slug, season } },
      { $sort: { ep_num: 1 } },
      { $project: {
        _id: 1, ep_num: 1, title: 1, title_missing: 1, thumb: 1,
        ok: { $gt: [{ $size: { $ifNull: ['$servers', []] } }, 0] },
      } },
    ]).toArray();
    const items = rows.map((e) => ({
      id: e._id, ep: e.ep_num,
      title: e.title_missing || !e.title ? `Episode ${e.ep_num}` : e.title,
      thumb: e.thumb || null, ok: !!e.ok,
    }));
    if (epCache.size > 2000) epCache.clear();
    epCache.set(k, { at: Date.now(), items });
    return items;
  }

  async function neighbours(ep) {
    const col = db.collection('episodes');
    const proj = { projection: { _id: 1 } };
    const [prev, next] = await Promise.all([
      col.find({ series_slug: ep.series_slug, $or: [{ season: ep.season, ep_num: { $lt: ep.ep_num } }, { season: { $lt: ep.season } }] }, proj)
        .sort({ season: -1, ep_num: -1 }).limit(1).toArray(),
      col.find({ series_slug: ep.series_slug, $or: [{ season: ep.season, ep_num: { $gt: ep.ep_num } }, { season: { $gt: ep.season } }] }, proj)
        .sort({ season: 1, ep_num: 1 }).limit(1).toArray(),
    ]);
    return { prev: prev[0] ? prev[0]._id : null, next: next[0] ? next[0]._id : null };
  }

  async function play(req, res, ctx) {
    const body = await readJson(req);
    const id = ctx.id;
    const att = W.playAttempt5.hit(id);
    if (att.count > CFG.lim.banPlayAttempts5Min) { await banUser(db, id, `5 minute mein ${att.count} episodes kholne ki koshish`); return fail(req, res, 403, 'banned'); }
    if (W.play5.peek(id) >= CFG.lim.playPer5Min) return fail(req, res, 429, 'slow_down', { retry: 60 });
    if (W.playDay.peek(id) >= CFG.lim.playPerDay) return fail(req, res, 429, 'daily_limit');

    let t, opts, nav = { prev: null, next: null }, label;
    if (typeof body.episode === 'string' && body.episode.length < 200) {
      const ep = await db.collection('episodes').findOne({ _id: body.episode },
        { projection: { series_slug: 1, season: 1, ep_num: 1, title: 1, title_missing: 1, servers: 1 } });
      if (!ep) return fail(req, res, 404, 'not_found');
      t = store.byKey.get(`series:${ep.series_slug}`);
      if (!t) return fail(req, res, 404, 'not_found');
      if (!ageGate(req, res, t, ctx)) return;
      opts = serverOptions(ep.servers);
      nav = await neighbours(ep);
      label = `S${ep.season} E${ep.ep_num}` + (ep.title && !ep.title_missing ? ` · ${ep.title}` : '');
    } else if (typeof body.movie === 'string' && body.movie.length < 200) {
      t = store.byKey.get(`movie:${body.movie}`);
      if (!t) return fail(req, res, 404, 'not_found');
      if (!ageGate(req, res, t, ctx)) return;
      const doc = await db.collection('titles').findOne({ _id: `movie:${body.movie}` }, { projection: { servers: 1 } });
      opts = serverOptions(doc && doc.servers);
      label = t.title;
    } else {
      return fail(req, res, 400, 'bad_request');
    }
    if (!opts.length) return fail(req, res, 404, 'no_video');
    W.play5.hit(id); W.playDay.hit(id);
    const token = makeToken(id, opts);
    json(req, res, 200, {
      title: t.title, label, token,
      player: `/p/${token}`,
      options: opts.map((o) => ({ n: o.n, name: o.name, lang: o.lang })),
      prev: nav.prev, next: nav.next,
      expires_in: CFG.tokenTtl,
    });
  }

  async function webhook(req, res) {
    if (req.headers['x-telegram-bot-api-secret-token'] !== CFG.webhookSecret) return fail(req, res, 403, 'no');
    const upd = await readJson(req);
    json(req, res, 200, { ok: true });
    const m = upd && upd.message;
    if (!m || !m.text || !m.chat) return;
    const app = CFG.miniAppUrl || CFG.publicUrl;
    if (/^\/start\b/.test(m.text) || /^\/help\b/.test(m.text)) {
      await tg(CFG.botToken, 'sendMessage', {
        chat_id: m.chat.id,
        text: `Namaste ${m.from && m.from.first_name ? m.from.first_name : ''}! 👋\nNeeche button dabao aur anime dekho.`,
        reply_markup: app ? { inline_keyboard: [[{ text: '▶️ Anime dekho', web_app: { url: app } }]] } : undefined,
      });
    }
  }

  return async function handler(req, res) {
    const url = new URL(req.url, 'http://x');
    const p = url.pathname;
    try {
      if (p === '/health') return json(req, res, 200, { ok: true, titles: store.list.length, loaded: new Date(store.loadedAt).toISOString() });

      const ip = clientIp(req);
      if (W.ip.hit(ip).count > CFG.lim.ipPerMin) return fail(req, res, 429, 'slow_down');

      if (p === `/tg/${CFG.webhookSecret}` && req.method === 'POST' && CFG.webhookSecret) return await webhook(req, res);

      if (p.startsWith('/p/')) {
        const tok = tokens.get(p.slice(3));
        if (!tok || Date.now() > tok.exp) return send(req, res, 410, '<!doctype html><body style="background:#000;color:#aaa;font:14px sans-serif;display:grid;place-items:center;height:100vh;margin:0">Link expire ho gaya. Wapas jaake dobara play dabao.</body>', { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store' });
        const o = Math.max(0, Math.min(tok.src.length - 1, +url.searchParams.get('o') || 0));
        return send(req, res, 200, playerHtml(tok.src[o]), {
          'content-type': 'text/html; charset=utf-8',
          'cache-control': 'no-store',
          'content-security-policy': "frame-ancestors 'self' https://web.telegram.org https://*.telegram.org",
        });
      }

      if (!p.startsWith('/api/')) return serveStatic(req, res, p);

      const ctx = await authed(req, res);
      if (!ctx) return;
      const q = url.searchParams;

      if (p === '/api/me' && req.method === 'GET') {
        return json(req, res, 200, { id: ctx.id, name: ctx.user.first_name || '', age: ctx.u.age });
      }

      if (p === '/api/age' && req.method === 'POST') {
        const body = await readJson(req);
        if (ctx.u.age === 'minor') return fail(req, res, 403, 'age_locked'); // ek baar "18 se kam" chuna to badal nahi sakte
        const age = body.adult === true ? 'adult' : body.adult === false ? 'minor' : null;
        if (!age) return fail(req, res, 400, 'bad_request');
        ctx.u.age = age;
        await db.collection('users').updateOne({ _id: ctx.id }, { $set: { age, age_at: new Date() } }, { upsert: true });
        return json(req, res, 200, { age });
      }

      if (p === '/api/home' && req.method === 'GET') {
        if (req.headers['if-none-match'] === store.homeEtag) { res.writeHead(304, { etag: store.homeEtag }); return res.end(); }
        const gz = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
        const body = gz ? store.homeGz : store.homeBody;
        const h = Object.assign({}, SEC_HEADERS, {
          'content-type': 'application/json; charset=utf-8', 'cache-control': 'private, max-age=60',
          etag: store.homeEtag, 'content-length': body.length,
        });
        if (gz) { h['content-encoding'] = 'gzip'; h.vary = 'Accept-Encoding'; }
        res.writeHead(200, h);
        return res.end(body);
      }

      if (p === '/api/meta' && req.method === 'GET') return json(req, res, 200, store.meta, 300);

      if (p === '/api/list' && req.method === 'GET') {
        return json(req, res, 200, listTitles({
          type: q.get('type'), genre: (q.get('genre') || '').slice(0, 60), lang: (q.get('lang') || '').slice(0, 40),
          sort: q.get('sort'), page: +q.get('page') || 1,
        }), 60);
      }

      if (p === '/api/search' && req.method === 'GET') {
        const text = (q.get('q') || '').slice(0, 80);
        return json(req, res, 200, search(text, { includeAdult: ctx.u.age !== 'minor', page: +q.get('page') || 1 }), 30);
      }

      let m = p.match(/^\/api\/title\/(series|movie)\/([^/]{1,150})$/);
      if (m && req.method === 'GET') {
        const t = store.byKey.get(`${m[1]}:${decodeURIComponent(m[2])}`);
        if (!t) return fail(req, res, 404, 'not_found');
        if (!ageGate(req, res, t, ctx)) return;
        return json(req, res, 200, {
          type: t.type, slug: t.slug, title: t.title, overview: t.overview, genres: t.genres, languages: t.languages,
          year: t.year, runtime: t.runtime, poster: t.poster, backdrop: t.backdrop, adult: t.adult,
          seasons: t.seasons, episodes: t.episodes, no_episodes: t.no_episodes,
        }, 120);
      }

      m = p.match(/^\/api\/title\/series\/([^/]{1,150})\/season\/(\d{1,3})$/);
      if (m && req.method === 'GET') {
        const slug = decodeURIComponent(m[1]);
        const t = store.byKey.get(`series:${slug}`);
        if (!t) return fail(req, res, 404, 'not_found');
        if (!ageGate(req, res, t, ctx)) return;
        return json(req, res, 200, { season: +m[2], items: await seasonEpisodes(slug, +m[2]) }, 120);
      }

      if (p === '/api/play' && req.method === 'POST') return await play(req, res, ctx);

      return fail(req, res, 404, 'not_found');
    } catch (e) {
      log('ERROR', req.method, p, e.message);
      if (!res.headersSent) fail(req, res, 500, 'server_error');
    }
  };
}

/* ------------------------------------------------------------------ */
/* Boot                                                                */
/* ------------------------------------------------------------------ */
async function refresh(db) {
  const docs = await db.collection('titles').find(
    { live: true, hidden: { $ne: true } },
    { projection: { servers: 0, downloads: 0, errors: 0, warnings: 0, flags: 0, fingerprint: 0 } },
  ).toArray();
  if (!docs.length && store.list.length) { log('refresh: 0 titles mile, purana data rakha'); return; }
  Object.assign(store, buildStore(docs));
  log(`catalog: ${store.list.length} titles (adult ${store.list.filter((t) => t.adult).length})`);
}

async function setupBot() {
  if (!CFG.botToken || !CFG.publicUrl) { log('BOT_TOKEN ya PUBLIC_URL nahi: bot setup chhoda'); return; }
  const r = await tg(CFG.botToken, 'setWebhook', {
    url: `${CFG.publicUrl}/tg/${CFG.webhookSecret}`, secret_token: CFG.webhookSecret,
    allowed_updates: ['message'], drop_pending_updates: true,
  });
  log('setWebhook:', r && r.ok ? 'ok' : JSON.stringify(r));
  const app = CFG.miniAppUrl || CFG.publicUrl;
  const m = await tg(CFG.botToken, 'setChatMenuButton', { menu_button: { type: 'web_app', text: 'Anime', web_app: { url: app } } });
  log('menu button:', m && m.ok ? 'ok' : JSON.stringify(m));
}

async function main() {
  if (!CFG.mongo) throw new Error('MONGO_URI set nahi hai');
  if (!CFG.botToken) log('WARNING: BOT_TOKEN nahi hai, koi bhi /api request pass nahi hogi');
  const { MongoClient } = require('mongodb');
  const client = new MongoClient(CFG.mongo, { maxPoolSize: 20 });
  await client.connect();
  const db = client.db(CFG.dbName);
  log('MongoDB connected');
  await refresh(db);
  const bans = await db.collection('users').find({ banned: true }, { projection: { _id: 1 } }).toArray();
  bans.forEach((b) => banned.add(String(b._id)));

  setInterval(() => refresh(db).catch((e) => log('refresh error', e.message)), CFG.refreshSec * 1000);
  setInterval(() => {
    Object.values(W).forEach((w) => w.sweep());
    const now = Date.now();
    for (const [k, v] of tokens) if (now > v.exp) tokens.delete(k);
    if (users.size > 50000) users.clear();
  }, 60e3);
  // admin ne Atlas se ban/unban kiya ho to har 2 minute sync
  setInterval(async () => {
    try {
      const list = await db.collection('users').find({ banned: true }, { projection: { _id: 1 } }).toArray();
      banned.clear(); list.forEach((b) => banned.add(String(b._id)));
      for (const [id, u] of users) u.banned = banned.has(id);
    } catch (e) { /* ignore */ }
  }, 120e3);

  const server = http.createServer(createHandler(db));
  server.keepAliveTimeout = 65e3;
  server.headersTimeout = 66e3;
  server.listen(CFG.port, () => log(`API chalu: port ${CFG.port}`));
  setupBot().catch((e) => log('bot setup error', e.message));
}

module.exports = { checkInitData, buildStore, search, listTitles, serverOptions, playerHtml, createHandler, store, CFG, W, banned, users, tokens, norm, isAdult };

if (require.main === module) {
  process.on('unhandledRejection', (e) => log('unhandledRejection', e && e.message));
  main().catch((e) => { console.error(e); process.exit(1); });
}
