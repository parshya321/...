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
  mangaBase: (env.MANGA_BASE || 'https://mangapark.cc').replace(/\/+$/, ''),
  mangaRefreshSec: +env.MANGA_REFRESH_SECONDS || 600,
  lim: {
    apiPerMin: +env.LIMIT_API_PER_MIN || 120,
    playPer5Min: +env.LIMIT_PLAY_PER_5MIN || 30,
    playPerDay: +env.LIMIT_PLAY_PER_DAY || 300,
    ipPerMin: +env.LIMIT_IP_PER_MIN || 240,
    banPlayAttempts5Min: +env.BAN_PLAY_ATTEMPTS_5MIN || 80,
    banBlockedPerMin: +env.BAN_BLOCKED_PER_MIN || 300,
    readPer5Min: +env.LIMIT_READ_PER_5MIN || 60,
    readPerDay: +env.LIMIT_READ_PER_DAY || 1500,
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
  read5: new Window(5 * 60e3), readDay: new Window(24 * 3600e3),
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
  popular: [], // plays ke hisaab se: ['series:slug', ...] (pichhle 7 din, alag users)
};
// "anime" = Japanese audio wala title (cartoon / western animation nahi)
const isAnime = (t) => (t.languages || []).some((l) => String(l).toLowerCase() === 'japanese');
// Movie collections shown on the Movies page
const COLLECTIONS = { shinchan: /shin[\s-]*chan/i, doraemon: /dor[ae][\s-]*e?mon/i };
const COLLECTION_NAMES = { shinchan: 'Shinchan movies', doraemon: 'Doraemon movies' };
const NOT_A_GENRE = /^(animation|anime)$/i; // har title animated hai, iska row bekaar

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
  const genres = count('genres').filter((g) => !NOT_A_GENRE.test(g.name));
  const languages = count('languages');
  const rows = genres.slice(0, 8).map((g) => ({
    title: g.name, genre: g.name,
    items: safe.filter((t) => t.genres.includes(g.name)).slice(0, 15).map(card),
  }));
  const anime = safe.filter(isAnime);
  const popular = [];
  for (const k of store.popular || []) { const t = byKey.get(k); if (t && !t.adult && isAnime(t)) popular.push(t); if (popular.length >= 20) break; }
  for (const t of anime) { if (popular.length >= 12) break; if (t.type === 'series' && !popular.includes(t)) popular.push(t); }
  const home = {
    hero: popular.slice(0, 5).map((t) => Object.assign(card(t), { backdrop: t.backdrop || null, genres: t.genres.slice(0, 3) })),
    popular: popular.slice(0, 20).map(card),
    latestAnime: anime.slice(0, 20).map(card),
    // Home shows anime only (no cartoons / western animated films)
    latest: anime.slice(0, 20).map(card),
    series: anime.filter((t) => t.type === 'series').slice(0, 20).map(card),
    movies: anime.filter((t) => t.type === 'movie').slice(0, 20).map(card),
    collections: Object.keys(COLLECTIONS).map((k) => ({
      key: k, title: COLLECTION_NAMES[k],
      items: safe.filter((t) => t.type === 'movie' && COLLECTIONS[k].test(t.title)).slice(0, 20).map(card),
    })).filter((c) => c.items.length),
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

function listTitles({ type, genre, lang, sort, page, collection }) {
  let arr = store.list.filter((t) => !t.adult);
  if (collection && COLLECTIONS[collection]) arr = arr.filter((t) => t.type === 'movie' && COLLECTIONS[collection].test(t.title));
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
  if (String(id).startsWith('g:')) return; // guests share IPs: slowed down, never banned
  if (banned.has(id)) return;
  banned.add(id);
  const u = users.get(id); if (u) u.banned = true;
  await db.collection('users').updateOne({ _id: id }, { $set: { banned: true, ban_reason: reason, banned_at: new Date() } }, { upsert: true }).catch(() => {});
  log('AUTO-BAN', id, reason);
  adminAlert(`🚫 Auto-ban: user ${id}\nReason: ${reason}`);
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

const imgSalt = 'srv:' + (process.env.BOT_TOKEN || 'ia').slice(-12); // stable per deploy, never sent to users
function serverOptions(servers) {
  const list = (servers || []).filter((s) => s && s.url && /^https:\/\//.test(s.url));
  // Users only ever see "Server N" + language - never the host name.
  // Order: multi-audio servers first (they play inside Telegram), then Hindi, English,
  // other Indian languages, Japanese.
  const RANK = ['hindi', 'english', 'tamil', 'telugu', 'malayalam', 'kannada', 'bengali', 'marathi', 'gujarati', 'odia', 'punjabi', 'japanese'];
  const rank = (s) => { const l = String(s.lang || '').trim().toLowerCase(); if (!l) return -1; const i = RANK.indexOf(l); return i < 0 ? 50 : i; };
  list.sort((a, b) => rank(a) - rank(b) || (a.order || 0) - (b.order || 0));
  return list.map((s, n) => {
    const l = String(s.lang || '').trim();
    // h = short anonymous id of the host, so the app can remember which server is fastest
    // for this user without ever seeing the host name
    let h = '';
    try { h = crypto.createHash('sha1').update(imgSalt + new URL(s.url).hostname).digest('hex').slice(0, 8); } catch (e) { /* bad url */ }
    return { n, label: l ? l.charAt(0).toUpperCase() + l.slice(1) : 'All languages + subtitles', url: s.url, h };
  });
}

function makeToken(userId, opts) {
  const t = crypto.randomBytes(18).toString('base64url');
  tokens.set(t, { u: userId, src: opts.map((o) => o.url), exp: Date.now() + CFG.tokenTtl * 1000 });
  return t;
}

const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));

function origin(u) { try { return new URL(u).origin; } catch (e) { return ''; } }
function playerHtml(src) {
  return `<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta name="referrer" content="no-referrer"><title>Player</title>${origin(src) ? `<link rel="preconnect" href="${esc(origin(src))}"><link rel="dns-prefetch" href="${esc(origin(src))}">` : ''}
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
// public/ folder na ho (phone se upload), to repo ke root wali index.html chalao. Root se sirf index.html, aur kuch nahi.
const ROOT_INDEX = path.join(__dirname, 'index.html');
function serveStatic(req, res, pathname) {
  let rel = decodeURIComponent(pathname).replace(/^\/+/, '');
  if (!rel || !path.extname(rel)) rel = 'index.html';
  if (rel === 'index.html' && !fs.existsSync(path.join(PUBLIC_DIR, 'index.html')) && fs.existsSync(ROOT_INDEX)) {
    if (!staticCache.has(ROOT_INDEX)) staticCache.set(ROOT_INDEX, { body: fs.readFileSync(ROOT_INDEX), type: MIME['.html'] });
    return send(req, res, 200, staticCache.get(ROOT_INDEX).body, { 'content-type': MIME['.html'], 'cache-control': 'no-cache' });
  }
  const file = path.normalize(path.join(PUBLIC_DIR, rel));
  if (!file.startsWith(PUBLIC_DIR)) return fail(req, res, 400, 'bad_path');
  let hit = staticCache.get(file);
  if (!hit) {
    if (!fs.existsSync(file)) {
      if (rel !== 'index.html') return fail(req, res, 404, 'not_found');
      return send(req, res, 200, 'API is running. The Mini App file is not uploaded yet.', { 'content-type': 'text/plain; charset=utf-8' });
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
/* ------------------------------------------------------------------ */
/* MANGA: catalog (memory), chapter pages (site se, jab user khole)    */
/* Anime se bilkul alag: alag store, alag search, alag routes          */
/* ------------------------------------------------------------------ */
const mstore = { list: [], bySlug: new Map(), home: null, genres: [], types: [], popular: [], loadedAt: 0 };

function mcard(m) {
  return { slug: m.slug, title: m.title, cover: m.cover || null, type: m.type || null, latest: m.latest != null ? m.latest : null };
}

function buildManga(docs) {
  const list = [], bySlug = new Map();
  for (const d of docs) {
    if (!d.title) continue;
    const m = {
      slug: d._id, title: d.title, cover: d.cover || null, genres: d.genres || [], type: d.type || null, status: d.status || null,
      year: d.year || null, authors: d.authors || [], chapters: d.chapterCount || 0, latest: d.latestNum != null ? d.latestNum : null,
      adult: !!d.adult, doujinshi: !!d.doujinshi,
      updated: d.updatedAt ? +new Date(d.updatedAt) : d.firstSeen ? +new Date(d.firstSeen) : 0,
    };
    m.n = norm(m.title); m.ns = squash(m.n);
    list.push(m); bySlug.set(m.slug, m);
  }
  list.sort((a, b) => b.updated - a.updated || a.title.localeCompare(b.title));
  const safe = list.filter((m) => !m.adult);
  const cnt = (f) => {
    const c = new Map();
    for (const m of safe) for (const g of [].concat(m[f] || [])) if (g) c.set(g, (c.get(g) || 0) + 1);
    return [...c].sort((a, b) => b[1] - a[1]).map(([name, n]) => ({ name, n }));
  };
  const genres = cnt('genres').filter((g) => g.name.toLowerCase() !== 'doujinshi');
  const types = cnt('type');
  const pop = [];
  for (const s of mstore.popular) { const m = bySlug.get(s); if (m && !m.adult) pop.push(m); if (pop.length >= 20) break; }
  for (const m of safe) { if (pop.length >= 12) break; if (!pop.includes(m) && m.chapters >= 20 && !m.doujinshi) pop.push(m); }
  const home = {
    popular: pop.map(mcard),
    latest: safe.filter((m) => !m.doujinshi).slice(0, 24).map(mcard),
    rows: types.slice(0, 3).map((t) => ({ title: t.name, type: t.name, items: safe.filter((m) => m.type === t.name && !m.doujinshi).slice(0, 15).map(mcard) })),
    genres: genres.slice(0, 40), types,
    total: safe.length,
  };
  return { list, bySlug, home, genres, types, loadedAt: Date.now() };
}

async function refreshManga(db) {
  const docs = await db.collection('manga').find({ live: true }, {
    projection: { title: 1, cover: 1, genres: 1, type: 1, status: 1, year: 1, authors: 1, chapterCount: 1, latestNum: 1, adult: 1, doujinshi: 1, updatedAt: 1, firstSeen: 1 },
  }).toArray();
  if (!docs.length && mstore.list.length) return;
  Object.assign(mstore, buildManga(docs));
  log(`manga catalog: ${mstore.list.length} titles`);
}

function mangaSearch(q, { includeAdult, page }) {
  const nq = norm(q);
  if (!nq) return { items: [], total: 0 };
  const words = nq.split(' '), sq = squash(nq), hits = [];
  for (const m of mstore.list) {
    if (m.adult && !includeAdult) continue;
    let s = 0;
    if (m.n === nq) s = 100;
    else if (m.n.startsWith(nq)) s = 80;
    else if ((' ' + m.n).includes(' ' + nq)) s = 65;
    else if (m.n.includes(nq)) s = 50;
    else if (words.every((w) => m.n.includes(w))) s = 40;
    else if (sq.length >= 3 && m.ns.includes(sq)) s = 30;
    if (s) hits.push([s - (m.doujinshi ? 5 : 0), m]);
  }
  hits.sort((a, b) => b[0] - a[0] || b[1].chapters - a[1].chapters);
  const p = Math.max(1, page || 1);
  return { total: hits.length, items: hits.slice((p - 1) * CFG.pageSize, p * CFG.pageSize).map((h) => mcard(h[1])), more: hits.length > p * CFG.pageSize };
}

function mangaList({ genre, type, status, sort, page }) {
  let arr = mstore.list.filter((m) => !m.adult);
  if (genre) { const g = genre.toLowerCase(); arr = arr.filter((m) => m.genres.some((x) => x.toLowerCase() === g)); }
  else arr = arr.filter((m) => !m.doujinshi);
  if (type) arr = arr.filter((m) => (m.type || '').toLowerCase() === type.toLowerCase());
  if (status) arr = arr.filter((m) => (m.status || '').toLowerCase() === status.toLowerCase());
  if (sort === 'az') arr = [...arr].sort((a, b) => a.title.localeCompare(b.title));
  else if (sort === 'chapters') arr = [...arr].sort((a, b) => b.chapters - a.chapters);
  else if (sort === 'year') arr = [...arr].sort((a, b) => (+b.year || 0) - (+a.year || 0));
  const p = Math.max(1, page || 1);
  return { total: arr.length, items: arr.slice((p - 1) * CFG.pageSize, p * CFG.pageSize).map(mcard), more: arr.length > p * CFG.pageSize };
}

// chapter ki photos: site se laao (yahan save nahi hoti), thodi der memory mein rakho
const pageCache = new Map(); // `${slug}|${key}` -> { at, pages }
const PAGE_TTL = 6 * 3600e3;
const imgHosts = new Set();
const UA = 'Mozilla/5.0 (Linux; Android 14) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0 Mobile Safari/537.36';

function parsePages(html) {
  const out = [], seen = new Set();
  const add = (u) => {
    if (!u) return;
    u = u.replace(/&amp;/g, '&').trim();
    if (!/^https?:\/\//i.test(u)) return;
    if (/\/cover\/|[-_/]cover[-_.]|logo|banner|avatar|icon|emoji|placeholder|loading|\/static\/|\?v=/i.test(u)) return;
    if (!/\.(png|jpe?g|webp|gif|avif)(\?|$)/i.test(u)) return;
    if (seen.has(u)) return;
    seen.add(u); out.push(u);
  };
  const tags = html.match(/<img\b[^>]*>/gi) || [];
  for (const t of tags) {
    const a = (n) => { const m = new RegExp('\\s' + n + '\\s*=\\s*["\']([^"\']+)["\']', 'i').exec(t); return m ? m[1] : ''; };
    add(a('data-src') || a('data-original') || a('data-lazy-src') || a('src'));
  }
  if (!out.length) { // img tags nahi mile: poore page mein image links dhundo
    for (const m of html.matchAll(/https?:\/\/[^"'\s<>\\]+?\.(?:png|jpe?g|webp|gif|avif)(?:\?[^"'\s<>\\]*)?/gi)) add(m[0]);
  }
  return out;
}

async function chapterPages(slug, key) {
  const k = `${slug}|${key}`;
  const c = pageCache.get(k);
  if (c && Date.now() - c.at < PAGE_TTL) return c.pages;
  const url = `${CFG.mangaBase}/read/${encodeURIComponent(slug)}/en/${encodeURIComponent(key)}`;
  let html = '';
  for (let i = 0; i < 2; i++) {
    const ac = new AbortController(); const tm = setTimeout(() => ac.abort(), 20000);
    try {
      const r = await fetch(url, { headers: { 'user-agent': UA, 'accept-language': 'en-US,en;q=0.9' }, signal: ac.signal });
      if (r.status === 404) throw Object.assign(new Error('not_found'), { code: 'not_found' });
      if (!r.ok) throw new Error('http_' + r.status);
      html = await r.text();
      break;
    } catch (e) { if (e.code === 'not_found' || i === 1) throw e; } finally { clearTimeout(tm); }
  }
  const pages = parsePages(html);
  if (!pages.length) throw Object.assign(new Error('no_pages'), { code: 'no_pages' });
  for (const u of pages) { try { imgHosts.add(new URL(u).host); } catch (e) { /* skip */ } }
  if (pageCache.size > 3000) pageCache.delete(pageCache.keys().next().value);
  pageCache.set(k, { at: Date.now(), pages });
  return pages;
}

// photo seedha na khule to hamare server se (backup). Link signed hai, koi aur use nahi kar sakta.
const imgSecret = crypto.createHash('sha256').update('img:' + (CFG.botToken || 'x')).digest();
const b64u = (s) => Buffer.from(s).toString('base64').replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
function proxyUrl(u) {
  const sig = crypto.createHmac('sha256', imgSecret).update(u).digest('hex').slice(0, 20);
  return `/mi/${sig}/${b64u(u)}`;
}
async function serveImage(req, res, sig, b64) {
  let u;
  try { u = Buffer.from(b64.replace(/-/g, '+').replace(/_/g, '/'), 'base64').toString('utf8'); } catch (e) { return fail(req, res, 400, 'bad_request'); }
  const want = crypto.createHmac('sha256', imgSecret).update(u).digest('hex').slice(0, 20);
  if (sig.length !== want.length || !crypto.timingSafeEqual(Buffer.from(sig), Buffer.from(want))) return fail(req, res, 403, 'no');
  let host; try { host = new URL(u).host; } catch (e) { return fail(req, res, 400, 'bad_request'); }
  if (!imgHosts.has(host)) return fail(req, res, 403, 'no');
  const ac = new AbortController(); const tm = setTimeout(() => ac.abort(), 30000);
  try {
    const r = await fetch(u, { headers: { 'user-agent': UA, referer: CFG.mangaBase + '/', accept: 'image/avif,image/webp,image/*,*/*' }, signal: ac.signal });
    const type = r.headers.get('content-type') || '';
    if (!r.ok || !/^image\//i.test(type)) { clearTimeout(tm); return fail(req, res, 502, 'image_failed'); }
    const len = +r.headers.get('content-length') || 0;
    if (len > 25e6) { clearTimeout(tm); return fail(req, res, 413, 'too_big'); }
    const buf = Buffer.from(await r.arrayBuffer());
    clearTimeout(tm);
    res.writeHead(200, Object.assign({}, SEC_HEADERS, { 'content-type': type, 'content-length': buf.length, 'cache-control': 'public, max-age=86400, immutable' }));
    return res.end(buf);
  } catch (e) { clearTimeout(tm); return fail(req, res, 502, 'image_failed'); }
}

const chapCache = new Map(); // slug -> { at, items }
async function mangaChapters(db, slug) {
  const c = chapCache.get(slug);
  if (c && Date.now() - c.at < 120e3) return c.items;
  const rows = await db.collection('manga_chapters').find({ slug }, { projection: { _id: 0, key: 1, num: 1, title: 1 } }).toArray();
  rows.sort((a, b) => (b.num == null ? -1 : b.num) - (a.num == null ? -1 : a.num) || String(b.key).localeCompare(String(a.key)));
  const items = rows.map((r) => {
    const t = String(r.title || '');
    const dm = /([A-Z][a-z]{2,8}\.? \d{1,2}, \d{4})\s*$/.exec(t);
    let label = (dm ? t.slice(0, dm.index) : t).trim();
    if (!label || /^chapter\s*$/i.test(label)) label = r.num != null ? `Chapter ${r.num}` : 'Oneshot';
    return { key: r.key, num: r.num, label, date: dm ? dm[1] : null };
  });
  if (chapCache.size > 1000) chapCache.clear();
  chapCache.set(slug, { at: Date.now(), items });
  return items;
}

async function refreshPopular(db) {
  const since = new Date(Date.now() - 7 * 86400e3);
  const [a, m] = await Promise.all([
    db.collection('plays').aggregate([
      { $match: { ts: { $gte: since } } },
      { $group: { _id: { t: '$type', s: '$slug' }, users: { $addToSet: '$user' } } },
      { $project: { n: { $size: '$users' } } }, { $sort: { n: -1 } }, { $limit: 60 },
    ]).toArray(),
    db.collection('manga_reads').aggregate([
      { $match: { ts: { $gte: since } } },
      { $group: { _id: '$slug', users: { $addToSet: '$user' } } },
      { $project: { n: { $size: '$users' } } }, { $sort: { n: -1 } }, { $limit: 60 },
    ]).toArray(),
  ]);
  store.popular = a.map((x) => `${x._id.t}:${x._id.s}`);
  mstore.popular = m.map((x) => x._id);
}

function createHandler(db) {
  async function authed(req, res) {
    const h = String(req.headers.authorization || '');
    const initData = h.startsWith('tma ') ? h.slice(4) : String(req.headers['x-init-data'] || '');
    const auth = checkInitData(initData, CFG.botToken, CFG.initDataMaxAge);
    if (!auth) {
      // Guest: opened outside Telegram, or Telegram did not pass login data (some phones / networks).
      // The app still opens. Guests never see 18+ titles, are never banned (many people share one
      // mobile-network IP), and are only slowed down when they send too many requests.
      const ip = clientIp(req);
      const gid = 'g:' + crypto.createHash('sha1').update(ip + '|' + String(req.headers['user-agent'] || '')).digest('hex').slice(0, 12);
      const ga = W.api.hit(gid);
      if (ga.count > CFG.lim.apiPerMin) { fail(req, res, 429, 'slow_down', { retry: Math.ceil((ga.reset - Date.now()) / 1000) }); return null; }
      return { id: gid, user: { id: gid, first_name: 'Guest' }, u: { age: 'minor', banned: false, seenWrite: 0, guest: true }, guest: true };
    }
    const id = String(auth.user.id);
    if (banned.has(id)) { fail(req, res, 403, 'banned'); return null; }
    const a = W.api.hit(id);
    if (a.count > CFG.lim.apiPerMin) {
      const b = W.blocked.hit(id);
      if (b.count > CFG.lim.banBlockedPerMin) await banUser(db, id, `${a.count}+ requests in 1 minute`);
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
    if (ctx.guest) { fail(req, res, 403, 'guest_adult'); return false; }
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
    if (att.count > CFG.lim.banPlayAttempts5Min) { await banUser(db, id, `tried to open ${att.count} episodes in 5 minutes`); return fail(req, res, 403, 'banned'); }
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
    const key = body.episode ? `ep:${body.episode}` : `movie:${body.movie}`;
    const short = body.episode ? label.split(' · ')[0] : 'Movie';
    const prev = watching.get(id);
    watching.set(id, { user: ctx.user, title: t.title, label: short, key, since: prev && prev.key === key ? prev.since : Date.now(), at: Date.now() });
    try { db.collection('plays').insertOne({ ts: new Date(), user: id, title: t.title, slug: t.slug, type: t.type, label: short }).catch(() => {}); } catch (e) { /* stats kabhi play nahi rokenge */ }
    // Next episode ready in advance: when the user taps Next the video starts at once,
    // without waiting for another round trip. Not counted as a play until it is opened.
    let pre = null;
    if (nav.next) {
      try {
        const nx = await db.collection('episodes').findOne({ _id: nav.next }, { projection: { servers: 1 } });
        const nopts = serverOptions(nx && nx.servers);
        if (nopts.length) pre = { episode: nav.next, player: `/p/${makeToken(id, nopts)}`, options: nopts.map((o) => ({ n: o.n, label: o.label, h: o.h })) };
      } catch (e) { /* optional */ }
    }
    json(req, res, 200, {
      title: t.title, label, token,
      player: `/p/${token}`,
      options: opts.map((o) => ({ n: o.n, label: o.label, h: o.h })),
      prev: nav.prev, next: nav.next, pre,
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
    const fromId = m.from ? String(m.from.id) : '';
    if (CFG.adminChat && fromId === String(CFG.adminChat) && ADMIN_CMDS.test(m.text)) {
      try { await adminCommand(db, m.text, m.chat.id); } catch (e) { await tg(CFG.botToken, 'sendMessage', { chat_id: m.chat.id, text: 'Error: ' + e.message }); }
      return;
    }
    if (/^\/start\b/.test(m.text) && m.from) {
      try {
        const r = await db.collection('bot_users').updateOne({ _id: fromId }, {
          $set: { first_name: m.from.first_name || '', last_name: m.from.last_name || '', username: m.from.username || '', lang: m.from.language_code || '', last_start: new Date() },
          $setOnInsert: { first_start: new Date() },
          $inc: { starts: 1 },
        }, { upsert: true });
        if (r && r.upsertedCount && process.env.NOTIFY_NEW_USERS !== '0') adminAlert(`🆕 New user: ${who(m.from)}`);
      } catch (e) { log('bot_users save fail', e.message); }
    }
    if (/^\/start\b/.test(m.text) || /^\/help\b/.test(m.text)) {
      await tg(CFG.botToken, 'sendMessage', {
        chat_id: m.chat.id,
        text: `Hi ${m.from && m.from.first_name ? m.from.first_name : ''}! 👋\nWelcome to Infinite Animes. Tap the button below to start watching.`,
        reply_markup: app ? { inline_keyboard: [[{ text: '▶️ Watch Anime', web_app: { url: app } }]] } : undefined,
      });
    }
  }

  return async function handler(req, res) {
    const url = new URL(req.url, 'http://x');
    const p = url.pathname;
    try {
      if (p === '/health') return json(req, res, 200, { ok: true, titles: store.list.length, loaded: new Date(store.loadedAt).toISOString() });

      // manga photo backup (signed link): ek chapter mein 50+ photos, isliye IP limit se pehle
      const mi = p.match(/^\/mi\/([0-9a-f]{20})\/([A-Za-z0-9_-]{8,3000})$/);
      if (mi && (req.method === 'GET' || req.method === 'HEAD')) return await serveImage(req, res, mi[1], mi[2]);

      const ip = clientIp(req);
      if (W.ip.hit(ip).count > CFG.lim.ipPerMin) return fail(req, res, 429, 'slow_down');

      if (p === `/tg/${CFG.webhookSecret}` && req.method === 'POST' && CFG.webhookSecret) return await webhook(req, res);

      if (p.startsWith('/p/')) {
        const tok = tokens.get(p.slice(3));
        if (!tok || Date.now() > tok.exp) return send(req, res, 410, '<!doctype html><body style="background:#000;color:#aaa;font:14px sans-serif;display:grid;place-items:center;height:100vh;margin:0">This link has expired. Go back and tap play again.</body>', { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store' });
        const o = Math.max(0, Math.min(tok.src.length - 1, +url.searchParams.get('o') || 0));
        let early = {};
        try { early = { link: `<${new URL(tok.src[o]).origin}>; rel=preconnect` }; } catch (e) { /* bad url: skip */ }
        return send(req, res, 200, playerHtml(tok.src[o]), {
          ...early,
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
        if (ctx.guest) return fail(req, res, 403, 'guest_adult'); // age can only be set from inside Telegram
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
          sort: q.get('sort'), page: +q.get('page') || 1, collection: (q.get('collection') || '').slice(0, 20),
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

      /* ---------- MANGA (anime se alag) ---------- */
      if (p === '/api/manga/home' && req.method === 'GET') {
        if (!mstore.home) return json(req, res, 200, { popular: [], latest: [], rows: [], genres: [], types: [], total: 0 });
        return json(req, res, 200, mstore.home, 60);
      }
      if (p === '/api/manga/list' && req.method === 'GET') {
        return json(req, res, 200, mangaList({
          genre: (q.get('genre') || '').slice(0, 60), type: (q.get('type') || '').slice(0, 20), status: (q.get('status') || '').slice(0, 20),
          sort: q.get('sort'), page: +q.get('page') || 1,
        }), 60);
      }
      if (p === '/api/manga/search' && req.method === 'GET') {
        return json(req, res, 200, mangaSearch((q.get('q') || '').slice(0, 80), { includeAdult: ctx.u.age !== 'minor', page: +q.get('page') || 1 }), 30);
      }
      m = p.match(/^\/api\/manga\/title\/([^/]{1,200})$/);
      if (m && req.method === 'GET') {
        const mg = mstore.bySlug.get(decodeURIComponent(m[1]));
        if (!mg) return fail(req, res, 404, 'not_found');
        if (!ageGate(req, res, mg, ctx)) return;
        const [doc, chapters] = await Promise.all([
          db.collection('manga').findOne({ _id: mg.slug }, { projection: { description: 1 } }),
          mangaChapters(db, mg.slug),
        ]);
        return json(req, res, 200, {
          slug: mg.slug, title: mg.title, cover: mg.cover, type: mg.type, status: mg.status, year: mg.year,
          authors: mg.authors, genres: mg.genres, adult: mg.adult, description: (doc && doc.description) || '', chapters,
        }, 120);
      }
      if (p === '/api/manga/read' && req.method === 'POST') {
        const body = await readJson(req);
        const slug = typeof body.slug === 'string' ? body.slug.slice(0, 200) : '';
        const key = typeof body.key === 'string' ? body.key.slice(0, 120) : '';
        const mg = mstore.bySlug.get(slug);
        if (!mg || !key) return fail(req, res, 404, 'not_found');
        if (!ageGate(req, res, mg, ctx)) return;
        if (W.read5.peek(ctx.id) >= CFG.lim.readPer5Min) return fail(req, res, 429, 'slow_down', { retry: 60 });
        if (W.readDay.peek(ctx.id) >= CFG.lim.readPerDay) return fail(req, res, 429, 'daily_limit');
        const ch = await db.collection('manga_chapters').findOne({ _id: `${slug}|${key}` }, { projection: { num: 1 } });
        if (!ch) return fail(req, res, 404, 'not_found');
        let pages;
        try { pages = await chapterPages(slug, key); } catch (e) {
          log('manga pages fail', slug, key, e.message);
          return fail(req, res, e.code === 'not_found' ? 404 : 502, e.code === 'no_pages' || e.code === 'not_found' ? 'no_pages' : 'source_down');
        }
        W.read5.hit(ctx.id); W.readDay.hit(ctx.id);
        const label = ch.num != null ? `Ch ${ch.num}` : 'Oneshot';
        const was = watching.get(ctx.id), wkey = `manga:${slug}|${key}`;
        watching.set(ctx.id, { user: ctx.user, title: '📖 ' + mg.title, label, key: wkey, since: was && was.key === wkey ? was.since : Date.now(), at: Date.now() });
        db.collection('manga_reads').insertOne({ ts: new Date(), user: ctx.id, slug, key, title: mg.title, label }).catch(() => {});
        return json(req, res, 200, { slug, key, label, pages: pages.map((u) => ({ u, b: proxyUrl(u) })) });
      }

      // player khula hai: har ~45 second "abhi dekh raha hai" update
      if (p === '/api/ping' && req.method === 'POST') {
        const w = watching.get(ctx.id);
        if (w) w.at = Date.now();
        return json(req, res, 200, { ok: true });
      }

      return fail(req, res, 404, 'not_found');
    } catch (e) {
      log('ERROR', req.method, p, e.message);
      if (!res.headersSent) fail(req, res, 500, 'server_error');
    }
  };
}

/* ------------------------------------------------------------------ */
/* Admin: kisne bot start kiya, kaun abhi dekh raha hai                */
/* Ye commands public bot pe sirf ADMIN_CHAT_ID wale ke liye chalte hain */
/* ------------------------------------------------------------------ */
const watching = new Map(); // userId -> { user, title, label, key, since, at }
const ONLINE_MS = 2 * 60e3;
const ADMIN_CMDS = /^\/(admin|stats|online|users|top|user|ban|unban)\b/;

function who(u) {
  const name = [u.first_name, u.last_name].filter(Boolean).join(' ') || 'No name';
  return `${name}${u.username ? ' @' + u.username : ''} (${u.id || u._id})`;
}
function ago(d) {
  const s = Math.max(0, Math.round((Date.now() - new Date(d).getTime()) / 1000));
  if (s < 60) return `${s}s ago`;
  if (s < 3600) return `${Math.round(s / 60)} min ago`;
  if (s < 86400) return `${Math.round(s / 3600)} h ago`;
  return `${Math.round(s / 86400)} days ago`;
}
function todayStart() { // midnight India time
  const off = 5.5 * 3600e3;
  return new Date(Math.floor((Date.now() + off) / 86400e3) * 86400e3 - off);
}
function onlineList() {
  const now = Date.now();
  return [...watching.entries()].filter(([, w]) => now - w.at < ONLINE_MS).sort((a, b) => b[1].at - a[1].at);
}

async function adminText(db, text) {
  const [cmd, arg] = text.trim().split(/\s+/);
  const c = cmd.replace(/@.*$/, '').toLowerCase();
  const day = todayStart();
  if (c === '/admin') {
    return ['Admin commands:', '/stats  : users, plays, watching now', '/online : who is watching right now', '/users  : latest 20 users who started the bot',
      '/top    : most watched today', '/user <id> : details of one user', '/ban <id>   /unban <id>'].join('\n');
  }
  if (c === '/stats') {
    const [botTotal, botToday, appTotal, appToday, playsToday, viewersToday] = await Promise.all([
      db.collection('bot_users').countDocuments({}), db.collection('bot_users').countDocuments({ first_start: { $gte: day } }),
      db.collection('users').countDocuments({}), db.collection('users').countDocuments({ last_seen: { $gte: day } }),
      db.collection('plays').countDocuments({ ts: { $gte: day } }), db.collection('plays').distinct('user', { ts: { $gte: day } }),
    ]);
    return [
      '📊 Infinite Animes stats',
      `👥 Bot started: ${botTotal} total, ${botToday} new today`,
      `📱 App opened: ${appTotal} total, ${appToday} active today`,
      `▶️ Plays today: ${playsToday} by ${viewersToday.length} people`,
      `🟢 Watching now: ${onlineList().length}`,
      `🚫 Banned: ${banned.size}`,
    ].join('\n');
  }
  if (c === '/online') {
    const list = onlineList();
    if (!list.length) return '🟢 Nobody is watching right now.';
    return `🟢 Watching now (${list.length})\n\n` + list.slice(0, 40).map(([, w]) =>
      `• ${who(w.user)}\n   ${w.title} ${w.label} · for ${Math.max(1, Math.round((Date.now() - w.since) / 60e3))} min`).join('\n');
  }
  if (c === '/users') {
    const list = await db.collection('bot_users').find({}).sort({ last_start: -1 }).limit(20).toArray();
    if (!list.length) return 'No users yet.';
    const total = await db.collection('bot_users').countDocuments({});
    return `👥 Latest users (${total} total)\n\n` + list.map((u) => `• ${who(u)}\n   joined ${ago(u.first_start)} · last /start ${ago(u.last_start)}`).join('\n');
  }
  if (c === '/top') {
    const rows = await db.collection('plays').aggregate([
      { $match: { ts: { $gte: day } } },
      { $group: { _id: '$title', n: { $sum: 1 }, people: { $addToSet: '$user' } } },
      { $sort: { n: -1 } }, { $limit: 15 },
    ]).toArray();
    if (!rows.length) return 'No plays today yet.';
    return '🔥 Most watched today\n\n' + rows.map((r, i) => `${i + 1}. ${r._id}: ${r.n} plays, ${r.people.length} people`).join('\n');
  }
  if (c === '/user') {
    if (!arg) return 'Use: /user <id>';
    const [b, a, plays] = await Promise.all([
      db.collection('bot_users').findOne({ _id: arg }), db.collection('users').findOne({ _id: arg }),
      db.collection('plays').find({ user: arg }).sort({ ts: -1 }).limit(10).toArray(),
    ]);
    if (!b && !a) return 'User not found.';
    const w = watching.get(arg);
    return [
      `👤 ${who(b || Object.assign({ id: arg }, a))}`,
      b ? `Started bot ${ago(b.first_start)}, ${b.starts || 1} times` : 'Never sent /start',
      a ? `Last opened app ${ago(a.last_seen)} · age: ${a.age || 'not asked'}` : 'Never opened the app',
      a && a.banned ? '🚫 Banned' : '',
      w && Date.now() - w.at < ONLINE_MS ? `🟢 Now watching: ${w.title} ${w.label}` : '',
      plays.length ? '\nLast watched:\n' + plays.map((p) => `• ${p.title} ${p.label} · ${ago(p.ts)}`).join('\n') : '',
    ].filter(Boolean).join('\n');
  }
  if (c === '/ban' || c === '/unban') {
    if (!/^\d+$/.test(arg || '')) return `Use: ${c} <id>`;
    const ban = c === '/ban';
    await db.collection('users').updateOne({ _id: arg }, { $set: { banned: ban, ...(ban ? { ban_reason: 'admin', banned_at: new Date() } : {}) } }, { upsert: true });
    if (ban) banned.add(arg); else banned.delete(arg);
    const u = users.get(arg); if (u) u.banned = ban;
    return ban ? `🚫 Banned ${arg}` : `✅ Unbanned ${arg}`;
  }
  return 'Unknown command. Send /admin';
}
async function adminCommand(db, text, chatId) {
  const out = await adminText(db, text);
  for (let i = 0; i < out.length; i += 3800) await tg(CFG.botToken, 'sendMessage', { chat_id: chatId, text: out.slice(i, i + 3800) });
}

/* ------------------------------------------------------------------ */
/* Boot                                                                */
/* ------------------------------------------------------------------ */
async function refresh(db) {
  const docs = await db.collection('titles').find(
    { live: true, hidden: { $ne: true } },
    { projection: { servers: 0, downloads: 0, errors: 0, warnings: 0, flags: 0, fingerprint: 0 } },
  ).toArray();
  if (!docs.length && store.list.length) { log('refresh: got 0 titles, keeping old data'); return; }
  Object.assign(store, buildStore(docs));
  log(`catalog: ${store.list.length} titles (adult ${store.list.filter((t) => t.adult).length})`);
}

async function setupBot() {
  if (!CFG.botToken || !CFG.publicUrl) { log('BOT_TOKEN or PUBLIC_URL missing: skipped bot setup'); return; }
  const r = await tg(CFG.botToken, 'setWebhook', {
    url: `${CFG.publicUrl}/tg/${CFG.webhookSecret}`, secret_token: CFG.webhookSecret,
    allowed_updates: ['message'], drop_pending_updates: true,
  });
  log('setWebhook:', r && r.ok ? 'ok' : JSON.stringify(r));
  const app = CFG.miniAppUrl || CFG.publicUrl;
  const m = await tg(CFG.botToken, 'setChatMenuButton', { menu_button: { type: 'web_app', text: 'Watch', web_app: { url: app } } });
  log('menu button:', m && m.ok ? 'ok' : JSON.stringify(m));
}

async function main() {
  if (!CFG.mongo) throw new Error('MONGO_URI is not set');
  if (!CFG.botToken) log('WARNING: BOT_TOKEN is missing, every /api request will be rejected');
  const { MongoClient } = require('mongodb');
  const client = new MongoClient(CFG.mongo, { maxPoolSize: 20 });
  await client.connect();
  const db = client.db(CFG.dbName);
  log('MongoDB connected');
  await refresh(db);
  try { await refreshManga(db); } catch (e) { log('manga refresh error', e.message); }
  try { await refreshPopular(db); await refresh(db); await refreshManga(db); } catch (e) { log('popular error', e.message); }
  await Promise.all([
    db.collection('manga_reads').createIndex({ ts: 1 }, { expireAfterSeconds: 30 * 86400 }),
    db.collection('plays').createIndex({ ts: 1 }, { expireAfterSeconds: 30 * 86400 }),
    db.collection('plays').createIndex({ user: 1, ts: -1 }),
    db.collection('bot_users').createIndex({ last_start: -1 }),
    db.collection('bot_users').createIndex({ first_start: -1 }),
    db.collection('users').createIndex({ last_seen: -1 }),
  ]).catch((e) => log('index error', e.message));
  const bans =await db.collection('users').find({ banned: true }, { projection: { _id: 1 } }).toArray();
  bans.forEach((b) => banned.add(String(b._id)));

  setInterval(() => refresh(db).catch((e) => log('refresh error', e.message)), CFG.refreshSec * 1000);
  setInterval(() => refreshManga(db).catch((e) => log('manga refresh error', e.message)), CFG.mangaRefreshSec * 1000);
  setInterval(() => refreshPopular(db).catch((e) => log('popular error', e.message)), 15 * 60e3);
  setInterval(() => {
    Object.values(W).forEach((w) => w.sweep());
    const now = Date.now();
    for (const [k, v] of tokens) if (now > v.exp) tokens.delete(k);
    for (const [k, v] of pageCache) if (now - v.at > PAGE_TTL) pageCache.delete(k);
    for (const [k, v] of watching) if (now - v.at > 30 * 60e3) watching.delete(k);
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
  server.listen(CFG.port, () => log(`API running on port ${CFG.port}`));
  setupBot().catch((e) => log('bot setup error', e.message));
}

module.exports = { parsePages, buildManga, mangaSearch, mangaList, mstore, proxyUrl, adminText, watching, todayStart, checkInitData, buildStore, search, listTitles, serverOptions, playerHtml, createHandler, store, CFG, W, banned, users, tokens, norm, isAdult };

if (require.main === module) {
  process.on('unhandledRejection', (e) => log('unhandledRejection', e && e.message));
  main().catch((e) => { console.error(e); process.exit(1); });
}
