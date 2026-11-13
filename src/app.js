(() => {
'use strict';
// ---------- data ----------
const B = JSON.parse(document.getElementById('bdata').textContent);
const XD = JSON.parse(document.getElementById('xdata').textContent);
const RACES = XD.R, NEEDS = XD.N, CIVIC = XD.E, RES = XD.RES;
const BT = new Map(B.map(b => [b.id, b]));
const CAT_ORDER = ['service','infrastructure','crafting','refining','extraction','husbandry','trade','military'];
const CAT_DE = { service:'Service', infrastructure:'Infrastructure', crafting:'Crafting', refining:'Refining', extraction:'Extraction', husbandry:'Husbandry', trade:'Trade', military:'Military' };
const css = getComputedStyle(document.documentElement);
const CAT_COL = Object.fromEntries(CAT_ORDER.map(c => [c, css.getPropertyValue('--c-' + c).trim()]));
const GOLD = css.getPropertyValue('--gold').trim();
const GOOD = css.getPropertyValue('--good').trim(), WARN = css.getPropertyValue('--warn').trim(), BAD = css.getPropertyValue('--bad').trim();
const ASSUMED = { canteen_normal: 100, bath_normal: 100, barber_normal: 100 };
const GROUPS = [
  { k:'fire',  n:'Fire',    need:'hearth',       t:['_hearth'], on:true },
  { k:'water', n:'Water',   need:'well',         t:['well_normal'], on:true },
  { k:'lav',   n:'Toilet', need:'constipation', t:['lavatory_normal'], on:true },
  { k:'food',  n:'Food',    need:'hunger',       t:['eatery_normal','canteen_normal'], on:true },
  { k:'talk',  n:'Speech',    need:'speaker',      t:['speaker_normal'], on:false },
  { k:'stage', n:'Stage',    need:'stage',        t:['stage_normal'], on:false },
  { k:'faith', n:'Faith',   need:'shrine',       t:B.filter(b => /^shrine_|^temple_/.test(b.id)).map(b => b.id), on:false },
  { k:'drink', n:'Drink',  need:'thirst',       t:['tavern_normal'], on:false },
  { k:'market',n:'Market',    need:'shopping',     t:['market_normal'], on:false },
  { k:'bath',  n:'Bath',     need:'bath',         t:['bath_normal'], on:false },
  { k:'justice',n:'Justice',  need:'court',        t:['_court'], on:false },
];
const HOME = new Set(['_home','_home_chamber']);
const WORKCAT = new Set(['extraction','husbandry','refining','crafting','trade','military','infrastructure']);
const isWalled = t => !!BT.get(t)?.wl;
const isOutdoor = t => !!BT.get(t)?.o;
const isFixed = t => !!BT.get(t)?.fx;
const imgs = new Map();
for (const b of B) { if (b.i) { const im = new Image(); im.src = b.i; imgs.set(b.id, im); } }
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&':'&amp;', '<':'&lt;', '>':'&gt;', '"':'&quot;' }[c]));
const fmt = (v, d = 1) => v.toLocaleString('en-US', { minimumFractionDigits: v !== 0 && Math.abs(v) < 10 ? d : 0, maximumFractionDigits: Math.abs(v) < 10 ? d : 0 });
const fmtPct = v => v >= .9995 ? '100 %' : (Math.round(v * 1000) / 10).toLocaleString('en-US', { minimumFractionDigits: 1, maximumFractionDigits: 1 }) + ' %';

// ---------- state ----------
let W = 190, H = 106;
let terr, occ, wcnt, dcnt, ceil;          // Boden/Straße/Mauer · Raum-uid · Wandring-Zähler · Tür-Zähler · Decke (0/1)
let blds = new Map();                     // uid -> {u,t,cells:[idx],d:[idx]} + abgeleitet: x,y,w,h,_set,_ring
let nextU = 1, gen = 0;
let radOv = {};
let tool = 'sel', prevTool = 'sel', curType = '_home', selU = 0, stampT = null, curTpl = null;
let ovMode = 'cov', covWho = 'home', distGroup = 'fire';
const groupOn = Object.fromEntries(GROUPS.map(g => [g.k, g.on]));
let planName = 'Example: residential and commercial block 37';
let calc = { resOv: {}, upf: 1, racesOn: false, races: {}, jewelry: false, days: 1, cap: {} };
function allocGrids() { terr = new Uint8Array(W * H); occ = new Int32Array(W * H); wcnt = new Uint8Array(W * H); dcnt = new Uint8Array(W * H); ceil = new Uint8Array(W * H); }
// Decken (Dach ohne Raum): auf freiem Boden oder Straße, nicht auf Räumen, Wandringen oder Mauern. Für „Roundness“, die Rechnung dazu fehlt noch.
const ceilOk = k => !occ[k] && !wcnt[k] && terr[k] !== 2;
allocGrids();

function radiusOf(t) { if (radOv[t] != null) return radOv[t]; const b = BT.get(t); if (b && b.r != null && b.r > 0) return b.r; return ASSUMED[t] ?? null; }
function radiusAssumed(t) { const b = BT.get(t); return radOv[t] == null && !(b && b.r > 0) && ASSUMED[t] != null; }
const inMap = (x, y) => x >= 0 && y >= 0 && x < W && y < H;
const D4 = [[1,0],[-1,0],[0,1],[0,-1]], D8 = [[1,0],[-1,0],[0,1],[0,-1],[1,1],[1,-1],[-1,1],[-1,-1]];

// ---------- building geometry (freie Formen) ----------
function rectCells(x, y, w, h) { if (w < 1 || h < 1 || x < 0 || y < 0 || x + w > W || y + h > H) return null; const a = []; for (let j = y; j < y + h; j++) for (let i = x; i < x + w; i++) a.push(j * W + i); return a; }
function bitsDecode(mask, w, h) { const by = fromB64u(mask), a = new Uint8Array(w * h); for (let k = 0; k < w * h; k++) a[k] = (by[k >> 3] >> (7 - (k & 7))) & 1; return a; }
function bitsEncode(a) { const by = new Uint8Array(Math.ceil(a.length / 8)); for (let k = 0; k < a.length; k++) if (a[k]) by[k >> 3] |= 1 << (7 - (k & 7)); return b64u(by); }
function maskCells(x, y, w, h, mask) {
  if (!mask) return rectCells(x, y, w, h);
  const a = bitsDecode(mask, w, h), out = [];
  for (let j = 0; j < h; j++) for (let i = 0; i < w; i++) if (a[j * w + i]) { if (!inMap(x + i, y + j)) return null; out.push((y + j) * W + x + i); }
  return out.length ? out : null;
}
function rotMask(mask, w, h) { if (!mask) return null; const a = bitsDecode(mask, w, h), b = new Uint8Array(w * h); for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) b[x * h + (h - 1 - y)] = a[y * w + x]; return bitsEncode(b); }
function ringOf(cells, set) {
  const r = new Set();
  for (const c of cells) { const x = c % W, y = (c / W) | 0; for (const [dx, dy] of D8) { const nx = x + dx, ny = y + dy; if (!inMap(nx, ny)) return null; const k = ny * W + nx; if (!set.has(k)) r.add(k); } }
  return r;
}
// Häuser aller Typen dürfen ohne Zwischenwand aneinanderstoßen (im Spiel geprüft, Better-Blueprints-Zeile „Barebone“ vom 10.11.2026).
// Der Wandring eines Hauses lässt Kacheln weg, die zu einem anderen Haus gehören; beim Setzen/Entfernen passen die Nachbarn ihren Ring an.
const HOME_T = '_home';
function homeAt(k) { const u = occ[k]; if (!u) return null; const b = blds.get(u); return b && b.t === HOME_T ? b : null; }
function homeSeam(o, s) {
  for (const c of o.cells) {
    const x = c % W, y = (c / W) | 0, seen = new Set();
    for (const [dx, dy] of D8) {
      const nx = x + dx, ny = y + dy; if (!inMap(nx, ny)) continue;
      const n = homeAt(ny * W + nx); if (!n || n === o || seen.has(n.u)) continue; seen.add(n.u);
      if (s > 0) { if (n._ring.delete(c)) wcnt[c]--; }
      else if (n._ring.size && !n._ring.has(c)) { n._ring.add(c); wcnt[c]++; }
    }
  }
}
// Türen bzw. Eingänge dürfen nicht in einem anderen Gebäude liegen
const doorsFree = (doors, ign = []) => { const ignU = new Set(ign.map(o => o.u)); return doors.every(i => !occ[i] || ignU.has(occ[i])); };
function mkB(o) {
  o.cells.sort((a, b) => a - b); o._set = new Set(o.cells);
  let x0 = W, y0 = H, x1 = -1, y1 = -1;
  for (const c of o.cells) { const x = c % W, y = (c / W) | 0; if (x < x0) x0 = x; if (x > x1) x1 = x; if (y < y0) y0 = y; if (y > y1) y1 = y; }
  o.x = x0; o.y = y0; o.w = x1 - x0 + 1; o.h = y1 - y0 + 1;
  o._ring = isWalled(o.t) ? (ringOf(o.cells, o._set) || new Set()) : new Set();
  if (o.t === HOME_T) for (const k of [...o._ring]) { const n = homeAt(k); if (n && n !== o) o._ring.delete(k); }   // Haus an Haus: keine Wand dazwischen (wie im Spiel)
  o._acc = null; if (isFixed(o.t)) { fxResolve(o); o.f = []; } else o.v = null; if (!o.f) o.f = []; return o;
}
const isRect = o => o.cells.length === o.w * o.h;
function maskOf(o) { if (isRect(o)) return null; const a = new Uint8Array(o.w * o.h); for (const c of o.cells) a[(((c / W) | 0) - o.y) * o.w + (c % W) - o.x] = 1; return bitsEncode(a); }
function orthAdj(i, set) { const x = i % W, y = (i / W) | 0; for (const [dx, dy] of D4) { const nx = x + dx, ny = y + dy; if (inMap(nx, ny) && set.has(ny * W + nx)) return true; } return false; }
function fitsCells(t, cells, ign = []) {
  if (!cells || !cells.length) return false;
  const ignU = new Set(ign.map(o => o.u)), set = new Set(cells);
  const ringIgn = k => { let n = 0; for (const o of ign) if (o._ring.has(k)) n++; return n; };
  const home = t === HOME_T;
  for (const c of cells) {
    const u = occ[c]; if (u && !ignU.has(u)) return false;
    if (wcnt[c] && wcnt[c] - ringIgn(c) > 0) {
      if (!home) return false;
      // Ein Haus darf auf den Wandring anderer Häuser, aber nicht auf deren Türen und nicht auf den Ring anderer Räume
      if (ownersOfRing(c).some(o => !ignU.has(o.u) && (o.t !== HOME_T || o.d.includes(c)))) return false;
    }
  }
  if (isWalled(t)) { const r = ringOf(cells, set); if (!r) return false; for (const k of r) { const u = occ[k]; if (u && !ignU.has(u) && !(home && blds.get(u)?.t === HOME_T)) return false; } }
  return true;
}
function stampB(o, s) {
  for (const c of o.cells) { occ[c] = s > 0 ? o.u : 0; if (s > 0) { terr[c] = 0; ceil[c] = 0; } }
  for (const k of o._ring) { wcnt[k] += s; if (s > 0) { terr[k] = 0; ceil[k] = 0; } }
  for (const i of o.d) dcnt[i] += s;
  if (o.t === HOME_T) homeSeam(o, s);
}
function validDoor(o, i) {
  if (i < 0 || i >= W * H || o._set.has(i) || !orthAdj(i, o._set)) return false;
  return isWalled(o.t) ? o._ring.has(i) : !occ[i];
}
function addB(t, cells, doorIdx = [], v = null) {
  const o = mkB({ u: nextU++, t, cells: [...cells], d: [], v });
  o.d = [...new Set(doorIdx)].filter(i => validDoor(o, i));
  if (isFixed(t) && !v && o.d.length) { o.v = null; fxResolve(o); }   // Ausrichtung aus den Türen ableiten (alte Pläne, Vorlagen ohne Variante)
  blds.set(o.u, o); stampB(o, 1); return o;
}
function liftB(o) { stampB(o, -1); blds.delete(o.u); }
function dropB(o) { blds.set(o.u, o); stampB(o, 1); }
function reshape(o, cells, doors) { liftB(o); o.cells = cells; mkB(o); fKeep(o); o.d = [...new Set(doors ?? o.d)].filter(i => validDoor(o, i)); dropB(o); }
function delB(u) { const o = blds.get(u); if (!o) return; liftB(o); if (selU === u) selU = 0; }
function rebuildGrids() {
  occ = new Int32Array(W * H); wcnt = new Uint8Array(W * H); dcnt = new Uint8Array(W * H);
  for (const o of blds.values()) for (const c of o.cells) occ[c] = o.u;
  for (const o of blds.values()) { mkB(o); for (const k of o._ring) wcnt[k]++; for (const i of o.d) dcnt[i]++; }
}
const outerOf = o => { const m = isWalled(o.t) ? 1 : 0; return { x: o.x - m, y: o.y - m, w: o.w + 2 * m, h: o.h + 2 * m }; };
const doorXY = o => o.d.map(i => [i % W, (i / W) | 0]);
function components(cells) {
  const set = new Set(cells), seen = new Set(), comps = [];
  for (const c of cells) {
    if (seen.has(c)) continue; const comp = [], st = [c]; seen.add(c);
    while (st.length) { const k = st.pop(); comp.push(k); const x = k % W, y = (k / W) | 0; for (const [dx, dy] of D4) { const nx = x + dx, ny = y + dy; if (!inMap(nx, ny)) continue; const n = ny * W + nx; if (set.has(n) && !seen.has(n)) { seen.add(n); st.push(n); } } }
    comps.push(comp);
  }
  return comps.sort((a, b) => b.length - a.length);
}
function ownersOfRing(k) { return [...blds.values()].filter(o => o._ring.has(k)); }
function boxHit(o, r) { const q = outerOf(o); return !(q.x > r.x + r.w - 1 || q.y > r.y + r.h - 1 || q.x + q.w - 1 < r.x || q.y + q.h - 1 < r.y); }

// ---------- Häuser: ein Raum = ein Möbelstück aus dem Spiel (HomeContructor, v71) ----------
// Gruppen in Spielreihenfolge; jede Gruppe hat 4 Drehungen. Reihen aus n Einheiten sind ein Möbelstück ohne Zwischenwand.
const HOUSE_BASES = [ { w:3, h:3, ex:1, max:9 }, { w:3, h:5, ex:1, max:15 }, { w:5, h:6, ex:2, max:30 } ];
const HOUSE_OFF = [0, 36, 96];
const SIDE_ROT = { bottom:0, left:1, top:2, right:3 }, SIDE_DE = { bottom:'bottom', left:'left', top:'top', right:'right' };
const HOUSE_SIZES_TXT = '3 × 3, 3 × 5, 5 × 6 or rows of them (e.g. 9 × 3, 15 × 5, 10 × 6), also rotated';
function rotCW(g) { const M = g.length, N = g[0].length, r = Array.from({ length: N }, () => Array(M)); for (let y = 0; y < M; y++) for (let x = 0; x < N; x++) r[x][M - 1 - y] = g[y][x]; return r; }
function houseGrid(bi, n, rot) {
  const b = HOUSE_BASES[bi], unit = [];
  for (let y = 0; y < b.h; y++) { const row = []; for (let x = 0; x < b.w; x++) row.push(x === 0 || y === 0 || x === b.w - 1 || y === b.h - 1 ? (y === b.h - 1 && x === b.ex ? 'e' : 'x') : '.'); unit.push(row); }
  let g = unit.map(row => { const r = []; for (let k = 0; k < n; k++) r.push(...row); return r; });
  for (let i = 0; i < rot; i++) g = rotCW(g);
  return g;
}
function houseFit(w, h, side) {
  const rot = SIDE_ROT[side], horiz = rot % 2 === 0;
  for (let bi = 0; bi < HOUSE_BASES.length; bi++) {
    const b = HOUSE_BASES[bi];
    if (horiz ? (h === b.h && w % b.w === 0 && w / b.w <= b.max) : (w === b.h && h % b.w === 0 && h / b.w <= b.max)) {
      const n = horiz ? w / b.w : h / b.w;
      return { bi, n, rot, side, id: 1 + HOUSE_OFF[bi] + (n - 1) * 4 + rot };
    }
  }
  return null;
}
// Eingänge relativ zur Innenfläche, als Kachel im Wandring
function houseEntrances(fit) {
  const g = houseGrid(fit.bi, fit.n, fit.rot), H = g.length, Wd = g[0].length, out = [];
  for (let y = 0; y < H; y++) for (let x = 0; x < Wd; x++) if (g[y][x] === 'e') out.push(fit.side === 'bottom' ? [x, H] : fit.side === 'top' ? [x, -1] : fit.side === 'left' ? [-1, y] : [Wd, y]);
  return out;
}
const houseSizeOk = (w, h) => ['bottom', 'left'].some(s => houseFit(w, h, s));
function doorSide(o, i) { const x = i % W, y = (i / W) | 0; if (y === o.y - 1) return 'top'; if (y === o.y + o.h) return 'bottom'; if (x === o.x - 1) return 'left'; if (x === o.x + o.w) return 'right'; return null; }
function houseCheck(o) {
  if (o.t !== '_home') return null;
  if (!isRect(o)) return { ok: false, msg: 'Houses must be rectangular.' };
  if (!houseSizeOk(o.w, o.h)) return { ok: false, msg: `${o.w} × ${o.h} does not exist in the game. Allowed: ${HOUSE_SIZES_TXT}.` };
  const sides = [...new Set(o.d.map(i => doorSide(o, i)).filter(Boolean))];
  if (!sides.length) return { ok: false, noDoor: true, msg: 'No door. Use W to put a door on the entrance side.' };
  if (sides.length > 1) return { ok: false, msg: 'Doors on several sides. Houses have their entrances on one side only.' };
  const fit = houseFit(o.w, o.h, sides[0]);
  if (!fit) return { ok: false, msg: `With ${o.w} × ${o.h} the entrances are not on the ${SIDE_DE[sides[0]]} side. Put the door on a long side.` };
  return { ok: true, fit, ent: houseEntrances(fit).map(([x, y]) => (o.y + y) * W + o.x + x), msg: `${fit.n} ${fit.n === 1 ? 'house' : 'houses'} ${HOUSE_BASES[fit.bi].w} × ${HOUSE_BASES[fit.bi].h}, entrance ${SIDE_DE[fit.side]}` };
}

// ---------- Räume mit fester Größe (usesArea() == false, v71): ein Raum = genau ein Möbelstück ----------
// Daten je Typ: fx.G = Gruppen in Spielreihenfolge, je Gruppe R = Zahl der Zusatzdrehungen und I = Grundformen.
// Zeichen: S Sprite+blockiert, s Sprite+begehbar, # ohne Sprite blockiert, . ohne Sprite begehbar, e Eingang (Wohnkammer).
// Index im Spiel: allItems[0] ist leer, dann je Gruppe je Größe die Grundform und ihre Drehungen (je 90° im Uhrzeigersinn).
const FXV = new Map();
function fxList(t) {
  if (FXV.has(t)) return FXV.get(t);
  const fx = BT.get(t)?.fx; if (!fx) { FXV.set(t, null); return null; }
  const out = []; let off = 1;
  fx.G.forEach((g, gi) => {
    g.I.forEach((base, si) => {
      let grid = base.map(r => [...r]);
      for (let r = 0; r <= g.R; r++) {
        if (r) grid = rotCW(grid);
        const h = grid.length, w = grid[0].length; let mx = -1, my = -1;
        for (let y = 0; y < h && mx < 0; y++) for (let x = 0; x < w; x++) if (grid[y][x] === 'S' || grid[y][x] === 's') { mx = x; my = y; break; }
        if (mx < 0) { mx = 0; my = 0; }
        const ent = [];
        for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) if (grid[y][x] === 'e') { if (y === 0) ent.push([x, -1]); else if (y === h - 1) ent.push([x, h]); else if (x === 0) ent.push([-1, y]); else if (x === w - 1) ent.push([w, y]); }
        out.push({ g: gi, s: si, r, R: g.R, w, h, grid, id: off + si * (g.R + 1) + r, mx, my, ent });
      }
    });
    off += g.I.length * (g.R + 1);
  });
  FXV.set(t, out); return out;
}
const fxFind = (t, g, s, r) => fxList(t)?.find(v => v.g === g && v.s === s && v.r === r) || null;
const fxSizes = t => (fxList(t) || []).filter(v => v.r === 0);
const fxMulti = t => (BT.get(t)?.fx.G.length || 0) > 1;
const fxGName = (t, g) => BT.get(t)?.fx.gn?.[g] || `Shape ${g + 1}`;
const fxName = (t, v) => t === '_home' ? `${fxGName(t, v.g)} · ${v.s + 1} ${v.s ? 'houses' : 'house'} · ${v.w} × ${v.h}` : `${v.w} × ${v.h}${fxMulti(t) ? ` · ${fxGName(t, v.g)}` : ''}`;
const fxSizesTxt = t => { const S = fxSizes(t); if (S.length > 16) return BT.get(t).fx.G.map((G, g) => { const v = S.find(x => x.g === g && x.s === 0); return `${fxGName(t, g)} ${v.w} × ${v.h}`; }).join(', ') + ', each as a row and rotated'; return [...new Set(S.map(v => `${v.w} × ${v.h}`))].join(', '); };
function fxOf(o) { if (!o.v || !isRect(o)) return null; const v = fxFind(o.t, o.v[0], o.v[1], o.v[2]); return v && v.w === o.w && v.h === o.h ? v : null; }
function fxResolve(o) {
  if (fxOf(o)) return;
  const L = fxList(o.t) || [], same = o.v ? L.filter(v => v.g === o.v[0] && v.s === o.v[1]) : [];
  const cand = isRect(o) ? (same.some(v => v.w === o.w && v.h === o.h) ? same : L).filter(v => v.w === o.w && v.h === o.h) : [];
  const score = v => o.d?.length && v.ent.length ? fxEntIdx(v, o.x, o.y).filter(i => o.d.includes(i)).length : 0;
  const hit = cand.length ? cand.reduce((a, b) => score(b) > score(a) ? b : a) : null;
  o.v = hit ? [hit.g, hit.s, hit.r] : null;
}
const fxEntIdx = (v, x, y) => v.ent.map(([dx, dy]) => (y + dy) * W + x + dx);
// Liegt ein Eingang in einem anderen Gebäude? (geht nur, seit Häuser ohne Zwischenwand aneinanderstoßen dürfen)
function entBlocked(o) { if (!isWalled(o.t)) return false; const v = fxOf(o); return !!v && fxEntIdx(v, o.x, o.y).some(i => occ[i] && occ[i] !== o.u); }
const fxCur = {};
function fxCurItem(t) { const c = fxCur[t]; return (c && fxFind(t, c.g, c.s, c.r)) || fxList(t)[0]; }
// E = eine Stufe größer, Q = eine Stufe kleiner (innerhalb der gewählten Form, wie im Spiel)
function fxCycle(t, dir) {
  const c = fxCurItem(t), n = fxPickN(t, c.g), s = Math.max(0, Math.min(n - 1, c.s + dir));
  if (s === c.s) { toast(dir > 0 ? 'This is already the largest variant.' : 'This is already the smallest variant.'); return; }
  fxCur[t] = { g: c.g, s, r: c.r };
}
function fxPickGroup(t, g) { const c = fxCurItem(t); fxCur[t] = { g, s: t === HOME_T ? Math.min(c.s, fxPickN(t, g) - 1) : 0, r: Math.min(c.r, BT.get(t).fx.G[g].R) }; }
function fxTurn(t) { const c = fxCurItem(t); fxCur[t] = { g: c.g, s: c.s, r: (c.r + 1) % (c.R + 1) }; }
const fxOrigin = (v, t) => ({ x: t.x - ((v.w - 1) >> 1), y: t.y - ((v.h - 1) >> 1) });

// ---------- Einrichtung: Möbeldaten (v71) ----------
// o.f = [[gruppe, größe, drehung, x, y], …] in Kartenkoordinaten (linke obere Ecke des gedrehten Möbelstücks)
const FD = JSON.parse(document.getElementById('fdata').textContent);
const AVN = ['ROOM', 'ROOM_SOLID', 'SOLID', 'NOT_ACCESSIBLE', 'AVOID_PASS', 'AVOID_LIKE_FUCK', 'PENALTY4', 'ENEMY'];
const FCH = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789!#$%()*+,-:;=?@^_{|}~';
const FSETS = new Map();
function fset(id) {
  if (FSETS.has(id)) return FSETS.get(id);
  const d = FD.S[id];
  const fs = {
    id, mustBeIndoors: !!d.in, empR: d.er || null, stats: d.st.map(([name, type]) => ({ name, type })),
    tileTypes: Object.fromEntries(d.tt.map(([a, m, k, dt], i) => [FCH[i], { availability: AVN[a], mustBeReachable: !!m, kind: k, data: dt || 0 }])),
    groups: d.g.map(g => ({ min: g.mn, max: g.mx, rotations: g.R, items: g.it.map(([rows, m]) => ({ tiles: rows.map(r => [...r].map(ch => ch === '.' ? null : ch)), multiplier: m, multiplierStats: m })) })),
  };
  FSETS.set(id, fs); return fs;
}
const canFurnish = t => !!FD.P[t];
function furnOf(t) { const P = FD.P[t]; if (!P) return null; const fs = fset(P.f); return { P, fs, bld: { id: t, storage: P.sto ?? 0, items: P.gs.map(s => ({ stats: s })) } }; }
const fTiles = (fs, g, s, r) => PC.getRotatedTiles(fs.groups[g].items[s], r);
const blocks = (fs, k) => PC.AVAIL_IMPASSABLE.has(fs.tileTypes[k]?.availability);
function fCells(fs, p) { const t = fTiles(fs, p[0], p[1], p[2]), out = []; for (let r = 0; r < t.length; r++) for (let c = 0; c < t[r].length; c++) if (t[r][c] != null) out.push([p[3] + c, p[4] + r, t[r][c]]); return out; }
// Index im Spiel (Furnisher.allItems): [0] leer, dann je Gruppe je Größe Grundform und Drehungen; Master = erste Kachel mit Sprite
function fItemId(fs, g, s, r) { let off = 1; for (let k = 0; k < g; k++) off += fs.groups[k].items.length * (fs.groups[k].rotations + 1); return off + s * (fs.groups[g].rotations + 1) + r; }
function fMaster(fs, t) {
  for (let y = 0; y < t.length; y++) for (let x = 0; x < t[y].length; x++) { const k = t[y][x]; if (k != null && fs.tileTypes[k]?.kind) return [x, y]; }
  for (let y = 0; y < t.length; y++) for (let x = 0; x < t[y].length; x++) if (t[y][x] != null) return [x, y];
  return [0, 0];
}
// Möbel behalten, die vollständig im (neuen) Raum liegen
function fKeep(o) {
  if (!o.f?.length) return; const fu = furnOf(o.t); if (!fu) { o.f = []; return; }
  o.f = o.f.filter(p => fu.fs.groups[p[0]]?.items[p[1]] && fCells(fu.fs, p).every(([x, y]) => inMap(x, y) && o._set.has(y * W + x)));
}
// Liste relativer Platzierungen um 90° im Uhrzeigersinn drehen (Rahmenhöhe H0), wie Gebäude und Vorlagen gedreht werden
function fRot(t, list, H0) {
  const fu = furnOf(t); if (!fu || !list) return [];
  const out = [];
  for (const [g, s, r, x, y] of list) {
    const G = fu.fs.groups[g]; if (!G) continue;
    const tl = fTiles(fu.fs, g, s, r), ih = tl.length, iw = tl[0].length;
    if (G.rotations === 0 && ih !== iw) continue;
    out.push([g, s, G.rotations === 0 ? 0 : (r + 1) % (G.rotations + 1), H0 - y - ih, x]);
  }
  return out;
}
const fRel = (o, dx, dy) => (o.f || []).map(([g, s, r, x, y]) => [g, s, r, x - dx, y - dy]);
const fAbs = (list, dx, dy) => (list || []).map(([g, s, r, x, y]) => [g, s, r, x + dx, y + dy]);
// Kontext für die Raumregeln: lokales Raster = Innenfläche plus 1 Kachel Rand
function fCtx(o, fu, f = o.f || []) {
  const gw = o.w + 2, gh = o.h + 2, x0 = o.x - 1, y0 = o.y - 1;
  const room = Array.from({ length: gh }, (_, r) => Array.from({ length: gw }, (_, c) => o._set.has((y0 + r) * W + x0 + c)));
  const doors = new Set(o.d.map(i => `${((i / W) | 0) - y0},${(i % W) - x0}`));
  const pl = f.map(([g, s, r, x, y]) => ({ groupIdx: g, itemIdx: s, rotation: r, row: y - y0, col: x - x0 }));
  const cx = PC.createRoomContext(fu.fs, fu.bld, room, pl, gw, gh, doors);
  cx.ext = extGrid(o, fu, gw, gh, x0, y0);
  return cx;
}
// Räume ohne Wand: Kacheln rund um den Raum, die im Plan frei sind (Boden oder Straße), zählen als Zugang für Möbel.
// Im Spiel lässt sich z. B. der 5 × 2-Stall in einen 5 × 2 großen Food Stall setzen.
function extGrid(o, fu, gw, gh, x0, y0) {
  if (fu.fs.mustBeIndoors) return null;
  const ext = new Uint8Array(gw * gh);
  for (let r = 0; r < gh; r++) for (let c = 0; c < gw; c++) {
    const x = x0 + c, y = y0 + r; if (!inMap(x, y)) continue; const k = y * W + x;
    if (o._set.has(k) || occ[k] || wcnt[k] || terr[k] === 2) continue;
    ext[r * gw + c] = 1;
  }
  return ext;
}
// Werte wie im Spiel (FurnisherStat, v71):
// Effizienz = 0,5 + 0,5 · Hilfswert / Arbeiter (max. 100 %), relativ = Wert / Hauptwert,
// Output (Production2) = Summe der OUT-Raten des ersten Rezepts · Arbeiter · Effizienz (ohne Tech-Boni).
// Arbeiter in Minen und Holzfällern hängen vom Gelände ab: Mine = freie Kacheln mit Vorkommen / 1,5, Holzfäller = Fläche · Fruchtbarkeit / 25.
const AREA_WORKERS = {
  mine: (o, cx) => { let n = 0; for (let r = 0; r < cx.gridH; r++) for (let c = 0; c < cx.gridW; c++) if (cx.room[r][c] && cx.occupancy[r][c] < 0) n++; return { n: Math.floor(n / 1.5), note: 'assumed: all free tiles lie on the deposit' }; },
  woodcutter: o => ({ n: Math.floor(o.cells.length / 25), note: 'assumed: soil 100 %' }),
};
const TERRAIN_OUT = new Set(['fishery', 'orchard']);
function fIdx(fs) {
  let emp = fs.stats.findIndex(s => s.type === 'employees'); if (emp < 0) emp = fs.stats.findIndex(s => s.type === 'employeesRelative'); if (emp < 0) emp = fs.stats.findIndex(s => s.type === 'custom' && /^(workers|men)$/.test(s.name));
  let prim = fs.stats.findIndex(s => s.type === 'services'); if (prim < 0) prim = emp >= 0 ? emp : 0;
  return { emp, prim, eff: fs.stats.findIndex(s => s.type === 'efficiency'), prod: fs.stats.findIndex(s => s.type === 'production') };
}
// Arbeiter und Effizienz aus einem Wertevektor v (Summe Gruppenwert · Größenfaktor)
function fCore(fu, v, aw) {
  const ix = fIdx(fu.fs), er = fu.fs.empR, wk = aw ? aw.n : er && ix.emp >= 0 && fu.fs.stats[ix.emp].type === 'employeesRelative' ? Math.ceil(v[er[0]] * er[1] - 1e-9) : ix.emp >= 0 ? v[ix.emp] : 0;
  let eff = null;
  if (ix.eff >= 0) { const o2 = ix.emp >= 0 || aw ? wk : v[ix.prim] || 0; eff = o2 ? Math.min(1, 0.5 + 0.5 * v[ix.eff] / o2) : (v[ix.eff] ? 1 : 0.5); }
  return { ix, wk, eff };
}
// Zugewinn an Effizienz (Prozentpunkte), wenn ein Möbelstück dieser Gruppe und Größe dazukäme
function fEffGain(o, fu, cx, g, s) {
  const ix = fIdx(fu.fs); if (ix.eff < 0 || !(fu.P.gs[g][ix.eff] > 0)) return null;
  const v = PC.computeStats(cx), aw = AREA_WORKERS[fu.fs.id]?.(o, cx), m = fu.fs.groups[g].items[s].multiplierStats;
  const v2 = v.map((x, i) => x + (fu.P.gs[g][i] || 0) * m);
  return Math.round((fCore(fu, v2, aw).eff - fCore(fu, v, aw).eff) * 100);
}
function fStats(o, fu, cx) {
  const fs = fu.fs, v = PC.computeStats(cx), P = fu.P, aw = AREA_WORKERS[fs.id]?.(o, cx), { ix, wk, eff } = fCore(fu, v, aw);
  const has = fs.stats.map((_, i) => P.gs.some(g => (g[i] || 0) !== 0) || ((i === ix.emp || i === ix.prod) && (aw || TERRAIN_OUT.has(fs.id))) || (i === ix.emp && fs.empR));
  return fs.stats.map((st, i) => {
    if (!has[i]) return null;
    const name = P.sn[i] || st.name.replace(/^./, c => c.toUpperCase());
    let txt, cls = '', num = v[i], note = '';
    if (i === ix.emp) { num = wk; txt = (aw ? '≈ ' : '') + (st.type === 'employeesRelative' || st.type === 'integer' ? String(Math.ceil(wk - 1e-9)) : fmt(wk, 1)); note = aw?.note || ''; }
    else if (st.type === 'efficiency') { num = eff; const over = wk > 0 ? v[i] - wk : 0; txt = Math.round(eff * 100) + ' %' + (over > 0.05 ? ` (helper value ${fmt(over, 1)} above need)` : ''); cls = eff >= .999 ? 'good' : eff >= .75 ? 'warn' : 'bad'; }
    else if (st.type === 'relative') { const qq = PC.bzQuality(fs, v); if (qq && qq.ri === i) num = qq.share; else { const o2 = v[ix.prim] || 0; num = o2 ? Math.min(1, v[i] / o2) : (v[i] ? 1 : 0); } txt = Math.round(num * 100) + ' %'; cls = num >= .999 ? 'good' : num >= .75 ? 'warn' : 'bad'; }
    else if (st.type === 'production') {
      if (TERRAIN_OUT.has(fs.id)) { num = null; txt = 'depends on the terrain'; }
      else { const rc = P.rc[Math.min(P.rc.length - 1, o.p?.rc ?? 0)] || [], e = eff ?? 1; num = rc.reduce((a, [, amt]) => a + amt, 0) * wk * e; txt = rc.length ? rc.map(([res, amt]) => `${fmt(amt * wk * e, 1)} ${resName(res)}`).join(' + ') + ' / day' : fmt(num, 1); }
    }
    else txt = st.type === 'integer' || st.type === 'services' ? String(Math.ceil(v[i] - 1e-9)) : fmt(v[i], 1);
    return { i, name, type: st.type, num, txt, cls, note, emp: i === ix.emp };
  }).filter(Boolean).concat((() => {
    // Qualität wie im Spiel (quality() der Instance-Klasse) und die wirksame Leistung daraus
    const qq = PC.bzQuality(fs, v); if (!qq) return [];
    const pn = P.sn[qq.pi] || fs.stats[qq.pi].name, cls = qq.quality >= .999 ? 'good' : qq.quality >= .75 ? 'warn' : 'bad';
    return [{ i: -1, name: 'Quality', type: 'quality', num: qq.quality, cls, txt: Math.round(qq.quality * 100) + ' %',
      note: `${qq.base ? `${Math.round(qq.base * 100)} % base value + ${Math.round((1 - qq.base) * 100)} % × share of helper furniture (${Math.round(qq.share * 100)} %)` : `equal to the share of helper furniture (${Math.round(qq.share * 100)} %)`}. Effective: ${fmt(qq.eff, 1)} of ${fmt(qq.P, 1)} ${pn}, before decay${qq.extra ? `; in operation × (0.5 + 0.5 × ${qq.extra}) on top` : ''}.` }];
  })());
}
// Output aller Rezepte bei aktuellen Arbeitern und Effizienz
function fRecipes(o, fu, cx) {
  const ix = fIdx(fu.fs); if (ix.prod < 0 || TERRAIN_OUT.has(fu.fs.id) || fu.P.rc.length < 2) return [];
  const v = PC.computeStats(cx), { wk, eff } = fCore(fu, v, AREA_WORKERS[fu.fs.id]?.(o, cx)), e = eff ?? 1;
  return fu.P.rc.map(rc => rc.map(([res, amt]) => `${fmt(amt * wk * e, 1)} ${resName(res)}`).join(' + '));
}

// ---------- Produktion je Gebäude (C1) ----------
// Arbeiter: Werkstätten/Veredler/Jäger aus der Einrichtung, Felder = Fläche · 7/576 (ROOM_FARM: Arbeitszeit 576 s / (4 + 3) s je Kachel),
// Weiden = Fläche · Boden / 64, Minen/Holzfäller geschätzt, Fischerei nur von Hand. Eigene Zahl (o.p.wo) hat Vorrang.
// Ausstoß/Tag = Rate des Rezepts · Arbeiter · Effizienz · Faktor; Felder/Plantagen: Faktor = Boden · (0,05 + Feuchte · Bonus) (RoomIrrigated).
const FARM_TPW = 576 / 7;
const isProd = t => !!BT.get(t)?.pk && BT.get(t).pk !== 'other';
function prodOf(o, raw = false) {
  const b = BT.get(o.t); if (!b?.rc || !isProd(o.t)) return null;
  const pp = o.p || {}, soil = (pp.soil ?? 100) / 100, moist = (pp.moist ?? 100) / 100, ri = Math.min(b.rc.length - 1, pp.rc ?? 0), rc = b.rc[ri];
  let wk = 0, src = '', eff = 1, factor = 1, note = '';
  const fu = furnOf(o.t);
  if (fu) { const cx = fCtx(o, fu), aw = AREA_WORKERS[fu.fs.id]?.(o, cx), core = fCore(fu, PC.computeStats(cx), aw); if (core.eff != null) eff = core.eff; if (aw) { wk = aw.n; src = 'estimated'; note = aw.note; } else if (core.ix.emp >= 0 && b.pk !== 'fish') { wk = core.wk; src = o.f.length ? 'from the furniture' : 'not furnished'; } }
  if (b.pk === 'farm') { wk = o.cells.length / FARM_TPW; src = 'from the area'; }
  if (b.pk === 'pasture') { wk = o.cells.length * soil / 64; src = 'from area and soil'; }
  if (b.pk === 'fish' && pp.wo == null) { src = 'please enter'; note = 'Fishery: workers depend on the water'; }
  if (pp.wo != null) { wk = pp.wo; src = 'by hand'; }
  if (b.pk === 'farm' || b.pk === 'orchard') factor = soil * (0.05 + moist * (b.ib ?? 1));
  // Boni (seit Version 31): ROOM_X auf Ausstoß und Verbrauch, Verbrauch zusätzlich ÷ ROOM_CONSUMPTION
  const X = raw ? { x: 1, cons: 1, parts: [] } : roomX(o, ri);
  const k = wk * eff * X.x, out = rc.o.map(([r, a]) => [r, a * k * factor]), inp = rc.i.map(([r, a]) => [r, a * k / X.cons]);
  return { b, ri, rc, wk, src, eff, factor, soil, moist, out, inp, note, X };
}

// ---------- Arbeiter je Raum wie im Spielcode (employees().neededSet / maxSet je Instance-Klasse) ----------
// need = benötigt, max = höchstens; est = geschätzt. Werte aus den Möbelstatistiken (Name der Statistik im Spiel).
const C = Math.ceil;
const FIXED_WORKERS = { speaker_normal: [1, 1], _home_chamber: [4, 4], _station: [15, 15], _builder: [1, 20] };
// Feste Räume, deren Arbeiter von der gewählten Größe abhängen: Multiplikator des Möbelstücks je Gruppe/Größe (aus den Constructor-Klassen)
// Version 28 (Phase 1b, Spielcode v71): Fight Pit = Möbelwert 5 × Faktor 2 (FIGHTPIT_NORMAL.txt, pit/ArenaConstructor), Loading Station = Ladekacheln (transport/Constructor, Job.job),
// Wasserpumpe = Arbeitskacheln bei Upgrade 0 (PumpConstructor.isJob: Upgrade ≤ tileData − 4). Version 30 (Spieltest Bene 12.11.2026): Loading Station 16 (MAX_EMPLOYEES), Bühne 8 bei allen Größen.
const FX_MUL = { _guard: [[1, 2, 3, 4, 5, 6, 7, 8], [2, 6, 9, 18]], _export: [[6, 8, 10, 12, 14, 16, 18, 40, 60]], _military_supply: [[2, 3, 4, 8]], _waterpump: [[6, 12, 18, 24]],
  fightpit_normal: [[10, 10]], _transport: [[16]], stage_normal: [[8, 8, 8]] };
const FX_WK = {
  _guard: m => ({ need: m, max: m }),
  _export: m => ({ need: C(m / 20), max: m, note: `${m} crates, one worker per 20 crates` }),
  _military_supply: m => ({ need: m, max: m * 4, note: `Depot size ${m}: needs ${m}, at most four times as many` }),
  _waterpump: (m, o) => { const u = o ? roomUp(o) : 0, n = m * (3 - u) / 3; return { need: n, max: n, note: u ? `Upgrade ${u}: ${n} instead of ${m} workers` : `without upgrade; with upgrade 1: ${m * 2 / 3}, with upgrade 2: ${m / 3}` }; },
  fightpit_normal: m => ({ need: m, max: m, note: 'furniture value 5 × factor 2, both sizes the same' }),
  _transport: m => ({ need: m, max: m, note: `${m} workers (MAX_EMPLOYEES in the game code, confirmed in the game)` }),
  stage_normal: m => ({ need: m, max: m, note: 'Stage: 8 workers for all sizes (game code, confirmed in the game)' }),
};
// Räume ohne eigene Arbeiter (Spielcode setzt keine employees)
const NO_WORKERS = new Set(['_import', '_execution', '_stocks', 'gatehouse_normal', 'artillery_catapult', '_hearth', '_home', 'well_normal', '_bench', '_throne', '_dump_corpse', '_watercanal', '_waterdrain', 'pool_moat', 'pool_pond', 'pool_stone']);
const isNoWorkers = t => NO_WORKERS.has(t) || /^(shrine|monument)_/.test(t);
const WK_RULE = {
  janitor: st => ({ need: C(st.workers / 5), max: st.workers }),
  canteen: st => ({ need: C(st.workers), max: C(st.workers * 2) }),
  inn: st => ({ need: C(st.workers), max: 2 * C(st.workers) }),
  eatery: st => ({ need: C(st.workers) }), market: st => ({ need: C(st.workers) }),
  lavatory: st => ({ need: C(st.workers), max: st.latrines }), barber: st => ({ need: C(st.workers), max: st.latrines }),
  nursery: st => ({ need: C(st.workers) }), breeder: st => ({ need: C(st.workers) }), laboratory: st => ({ need: C(st.workers) }),
  cannibal: st => ({ need: C(st.workers / 2), max: st.workers }),
  tavern: st => ({ need: C(st.tables / 4), max: C(st.tables / 2) }),
  bath: st => ({ need: C(st.baths / 1.5), max: st.baths }),
  school: st => ({ need: Math.floor(st.stations / 8), max: Math.floor(st.stations / 3) }),
  university: st => ({ need: st.students, max: st.students }),
  pleasure: st => ({ need: st.beds, max: st.beds }),
  police: st => ({ need: st.prisoners, max: st.prisoners * 3 }),
  court: st => ({ need: st.workers, max: st.workers }),
  prison: st => ({ need: C(st.guards), max: C(st.guards) }), asylum: st => ({ need: C(st.guards), max: C(st.guards) }),
  physician: st => ({ need: C(st.workers), max: C(st.workers) }),
  resthome: st => ({ need: C(st.stations - 1e-9), max: C(st.stations - 1e-9), note: 'Retirement home: as many as places (fewer only if free tiles are missing in the room)' }),
  orchard: st => ({ need: C(st.workers), max: Math.floor(st.workers * 1.25) }),
  stockpile: st => ({ need: null, max: C(st.storage) * 8, note: 'Warehouse: as many haulers as you set in the game (at most 8 per crate)' }),
};
function workersOf(o) {
  const b = BT.get(o.t); if (!b) return null;
  if (o.p?.wo != null) { const n = C(o.p.wo - 1e-9); return { need: n, max: n, src: 'by hand' }; }
  if (isNoWorkers(o.t)) return { need: 0, none: 1 };
  if (FIXED_WORKERS[o.t]) { const [n, m] = FIXED_WORKERS[o.t]; return { need: n, max: m }; }
  if (isFixed(o.t)) {
    const v = fxOf(o);
    if (o.t === '_hauler') return { need: 1, max: Math.max(o.w, o.h) * 5 };
    if (v && FX_MUL[o.t]) { const m = FX_MUL[o.t][v.g]?.[v.s]; if (m != null) return FX_WK[o.t](m, o); }
    return { need: null, unk: 1, note: 'Worker count for this fixed room not read out, please check in the game' };
  }
  if (o.t === '_stockade') { // Constructor: Gefangene = 0,25 × Innenkacheln (alle 8 Nachbarn im Raum), Arbeiter = 0,1 × Gefangene
    const S = new Set(o.cells); let n = 0;
    for (const c of o.cells) { const x = c % W, y = (c / W) | 0; let ok = true; for (let dy = -1; dy <= 1 && ok; dy++) for (let dx = -1; dx <= 1; dx++) if ((dx || dy) && !S.has((y + dy) * W + x + dx)) { ok = false; break; } if (ok) n++; }
    const w = C(0.1 * n * 0.25 - 1e-9); return { need: w, max: w, note: `${fmt(n * 0.25, 1)} prisoners, 1 worker per 10` };
  }
  if (b.pk === 'farm') { const j = C(o.cells.length / FARM_TPW - 1e-9); return { need: j, max: Math.floor(j * 1.5), est: 0 }; }
  const fu = furnOf(o.t); if (!fu) return null;
  const cx = fCtx(o, fu), v = PC.computeStats(cx), st = {};
  fu.fs.stats.forEach((x, i) => { st[x.name] = v[i]; });
  if (fu.fs.empR) st.workers = C(v[fu.fs.empR[0]] * fu.fs.empR[1] - 1e-9);
  const rule = WK_RULE[fu.fs.id];
  if (rule) { const r = rule(st); return { ...r, est: r.est || 0, src: o.f.length ? '' : 'not furnished' }; }
  const pr = isProd(o.t) ? prodOf(o) : null;
  if (pr) { const n = C(pr.wk - 1e-9); return { need: n, max: fu.fs.id === 'pasture' ? n * 2 : n, est: pr.src === 'estimated' ? 1 : 0, src: pr.src }; }
  const k = ['workers', 'men', 'priests', 'guards'].find(n => st[n] != null);
  if (k) return { need: C(st[k] - 1e-9), max: C(st[k] - 1e-9), src: o.f.length ? '' : 'not furnished' };
  return null;
}
const wkTxt = w => w ? (w.none ? 'none' : w.unk ? 'unknown' : w.need == null ? `as set${w.max != null ? ` · at most ${w.max}` : ''}` : `${w.est ? '≈ ' : ''}${w.need} needed${w.max != null && w.max !== w.need ? ` · at most ${w.max}` : ''}`) : '';
// Kurzfassung für Auswahl-Panel und Arbeitsplatz-Rechnung
function fSummary(o) {
  const fu = furnOf(o.t); if (!fu || !o.f?.length) return null;
  const cx = fCtx(o, fu), st = fStats(o, fu, cx);
  return { n: o.f.length, st, workers: st.find(x => x.emp)?.num ?? null };
}

// ---------- undo ----------
const undoS = [], redoS = [];
const undoCap = () => Math.max(15, Math.min(120, Math.floor(3e7 / (W * H))));
function snap() { return { W, H, terr: terr.slice(), ceil: ceil.slice(), b: [...blds.values()].map(o => ({ u: o.u, t: o.t, cells: [...o.cells], d: [...o.d], v: o.v ? [...o.v] : null, f: (o.f || []).map(p => [...p]), p: o.p ? { ...o.p } : null })), nextU, radOv: { ...radOv } }; }
function restore(s) {
  W = s.W; H = s.H; terr = s.terr.slice(); ceil = s.ceil ? s.ceil.slice() : new Uint8Array(W * H); blds = new Map(s.b.map(o => [o.u, { ...o, cells: [...o.cells], d: [...o.d], v: o.v ? [...o.v] : null, f: (o.f || []).map(p => [...p]), p: o.p ? { ...o.p } : null }])); nextU = s.nextU; radOv = { ...s.radOv };
  rebuildGrids(); if (!blds.has(selU)) selU = 0; syncSizeInputs(); computeSelReach(); dirty(); if (ed) edSync();
}
function commit() { undoS.push(snap()); while (undoS.length > undoCap()) undoS.shift(); redoS.length = 0; }
function undo() { if (!undoS.length) return; msel = null; redoS.push(snap()); restore(undoS.pop()); }
function redo() { if (!redoS.length) return; msel = null; undoS.push(snap()); restore(redoS.pop()); }

// ---------- reach (BFS) ----------
let distBy = new Map(), reachDirty = true;
function walkable(i) {
  if (terr[i] === 2) return false;
  if (wcnt[i] && !dcnt[i]) return false;
  const u = occ[i]; if (!u) return true;
  const o = blds.get(u); return !!(o && isOutdoor(o.t));
}
function accessTiles(o) {
  if (o._acc && o._accGen === gen) return o._acc;
  let out;
  if (o.d.length) out = o.d.filter(walkable);
  else {
    const s = new Set();
    const look = (from) => { const x = from % W, y = (from / W) | 0; for (const [dx, dy] of D4) { const nx = x + dx, ny = y + dy; if (!inMap(nx, ny)) continue; const k = ny * W + nx; if (o._set.has(k) || o._ring.has(k)) continue; if (walkable(k)) s.add(k); } };
    if (isWalled(o.t)) { for (const r of o._ring) if (orthAdj(r, o._set)) look(r); }
    else for (const c of o.cells) look(c);
    out = [...s];
  }
  o._acc = out; o._accGen = gen; return out;
}
const bfsBuf = { n: 0, dist: null, q: null };
function bfsRaw(sources, maxD) {
  const N = W * H;
  if (bfsBuf.n !== N) { bfsBuf.n = N; bfsBuf.dist = new Uint16Array(N).fill(65535); bfsBuf.q = new Int32Array(N); }
  const dist = bfsBuf.dist, q = bfsBuf.q; let h = 0, t = 0;
  for (const i of sources) if (dist[i] !== 0) { dist[i] = 0; q[t++] = i; }
  while (h < t) {
    const i = q[h++], d = dist[i]; if (d >= maxD) continue;
    const x = i % W, nd = d + 1;
    if (x > 0) { const n = i - 1; if (dist[n] === 65535 && walkable(n)) { dist[n] = nd; q[t++] = n; } }
    if (x < W - 1) { const n = i + 1; if (dist[n] === 65535 && walkable(n)) { dist[n] = nd; q[t++] = n; } }
    if (i >= W) { const n = i - W; if (dist[n] === 65535 && walkable(n)) { dist[n] = nd; q[t++] = n; } }
    if (i < N - W) { const n = i + W; if (dist[n] === 65535 && walkable(n)) { dist[n] = nd; q[t++] = n; } }
  }
  return { dist, q, t };
}
function bfsReset(r) { for (let k = 0; k < r.t; k++) r.dist[r.q[k]] = 65535; }
function bfs(sources, maxD) { const r = bfsRaw(sources, maxD), out = new Uint16Array(W * H).fill(65535); for (let k = 0; k < r.t; k++) out[r.q[k]] = r.dist[r.q[k]]; bfsReset(r); return out; }
function computeReach() {
  distBy = new Map(); const byType = new Map();
  for (const o of blds.values()) { if (radiusOf(o.t) == null) continue; if (!byType.has(o.t)) byType.set(o.t, []); byType.get(o.t).push(o); }
  for (const [t, list] of byType) distBy.set(t, bfs(list.flatMap(accessTiles), radiusOf(t)));
  reachDirty = false;
}
function groupDistAt(g, i) { let m = 65535; for (const t of g.t) { const d = distBy.get(t); if (d && d[i] < m && d[i] <= radiusOf(t)) m = d[i]; } return m; }
function groupMaxR(g) { let m = 0; for (const t of g.t) if (distBy.has(t)) m = Math.max(m, radiusOf(t)); return m || 100; }
function bldCovered(o, g) { for (const i of accessTiles(o)) if (groupDistAt(g, i) !== 65535) return true; return false; }

// ---------- Einwohner, Bedarf, Auslastung ----------
const houseKey = o => isRect(o) ? `${Math.min(o.w, o.h)}×${Math.max(o.w, o.h)}` : `F${o.cells.length}`;
const houseLabel = k => k[0] === 'F' ? `Free shape, ${k.slice(1)} tiles` : k.replace('×', ' × ');
const houseDefault = o => Math.max(1, Math.floor(o.cells.length / 3));
function residentsOf(o) { if (o.t !== '_home') return 0; const v = calc.resOv[houseKey(o)]; return (v != null ? v : houseDefault(o)) * (calc.upf > 0 ? calc.upf : 1); }
function raceShares() {
  if (!calc.racesOn) return null;
  const on = RACES.filter(r => calc.races[r.id]?.on), sum = on.reduce((s, r) => s + (calc.races[r.id].share || 0), 0);
  if (!on.length || sum <= 0) return null; return on.map(r => ({ r, f: (calc.races[r.id].share || 0) / sum }));
}
function needMult(needId) { const sh = raceShares(); if (!sh) return 1; return sh.reduce((s, { r, f }) => s + f * (r.m[needId] ?? 1), 0); }
let load = null, loadStale = true;
function computeLoad() {
  const houses = [...blds.values()].filter(o => o.t === '_home');
  const hAcc = houses.map(accessTiles), res = houses.map(residentsOf), per = {};
  for (const g of GROUPS) {
    const sb = [...blds.values()].filter(o => g.t.includes(o.t));
    const best = new Float64Array(houses.length).fill(Infinity), who = new Int32Array(houses.length);
    for (const b of sb) {
      const R = radiusOf(b.t); if (R == null) continue;
      const r = bfsRaw(accessTiles(b), R);
      for (let hi = 0; hi < houses.length; hi++) { let m = Infinity; for (const i of hAcc[hi]) { const d = r.dist[i]; if (d !== 65535 && d < m) m = d; } if (m < best[hi]) { best[hi] = m; who[hi] = b.u; } }
      bfsReset(r);
    }
    const byB = new Map(sb.map(b => [b.u, 0]));
    for (let hi = 0; hi < houses.length; hi++) if (who[hi]) byB.set(who[hi], byB.get(who[hi]) + res[hi]);
    per[g.k] = { byB, who };
  }
  load = { houses, res, per }; loadStale = false;
}
const capOf = g => { const v = calc.cap[g.k]; return v > 0 ? v : null; };
function loadState(g, u) { const cap = capOf(g); if (!cap || !load) return 0; const v = load.per[g.k].byB.get(u) || 0; return v > cap ? 2 : v > cap * 0.8 ? 1 : 0; }

// ---------- templates ----------
// T = { id, n, s, w, h, ter:[[v,x,y,w,h]], b:[[type,x,y,w,h,[[dx,dy]],mask?]] } — Koordinaten relativ zur Außenkante
// Eingebaute Vorlagen: Benes Better-Blueprints-Zeile „Vorlagen“ (10.11.2026), umgewandelt mit skripte/bb2tpl.mjs → tdata71.json.
// Baukasten für Blöcke 37 × 37: Ecken 13 × 13, Streifen 7 × 13, Mitte 7 × 7; Teile liegen wie oben links bzw. oben, R dreht sie weiter.
const BUILTIN = JSON.parse(document.getElementById('tdata').textContent);
const TPL_CATS = [['raster', 'Street grids'], ['bloecke', 'Complete blocks'], ['wohnen', 'Residential'], ['gewerbe', 'Commercial'], ['svc1', 'Services, small'], ['svc2', 'Services, double']];
const TPL_OWN = 'Custom';
// Syx Pack v35: category names were German before. Own templates and the open/closed state keep working with the old names.
const CAT_MIG = { 'Straßenraster': 'Street grids', 'Komplette Blöcke': 'Complete blocks', 'Wohnen': 'Residential', 'Gewerbe': 'Commercial', 'Service klein': 'Services, small', 'Service doppelt': 'Services, double', 'Eigene': 'Custom' };
const tplById = id => BUILTIN.find(T => T.id === id);
// Raster-Generator (seit Version 28, Straßenbreite seit Version 30): n × m Baukasten-Blöcke wie „Raster 37 × 37“.
// Je Block 35 Kacheln innen mit Innenstraßen (1 breit) auf 13 und 21 ab Innenkante, also 14 und 22 ab Blockstraße.
// Straßen zwischen den Blöcken k breit (1–9), Außenrand k oder 1 breit. k = 1: Nachbarblöcke teilen die Randstraße, Fläche (36·n+1) × (36·m+1).
const GRID_IN = 35, GRID_INNER = [13, 21];
function gridLines(n, k, rim) {
  const out = [], e = rim ? k : 1; let p = 0;
  for (let i = 0; i <= n; i++) {
    const wd = i === 0 || i === n ? e : k; out.push([p, wd]); p += wd;
    if (i < n) { for (const o of GRID_INNER) out.push([p + o, 1]); p += GRID_IN; }
  }
  return { lines: out, len: p };
}
function gridTpl(s) {
  const k = s.k ?? 1, rim = s.rim ?? true, X = gridLines(s.nx, k, rim), Y = gridLines(s.ny, k, rim), ter = [];
  for (const [x, wd] of X.lines) ter.push([1, x, 0, wd, Y.len]);
  for (const [y, wd] of Y.lines) ter.push([1, 0, y, X.len, wd]);
  return { id:'grid', n:`Raster ${s.nx} × ${s.ny} blocks`, s:`Kit 37 × 37${k > 1 ? `, block streets ${k} wide${rim ? '' : ', edge 1'}` : ''}`, w: X.len, h: Y.len, ter, cl: [], b: [] };
}
function rotTpl(T) {
  const H0 = T.h, rr = (x, y, w, h) => [H0 - y - h, x, h, w];
  return { ...T, w: T.h, h: T.w,
    ter: T.ter.map(([v, x, y, w, h]) => [v, ...rr(x, y, w, h)]),
    cl: (T.cl || []).map(([x, y, w, h]) => rr(x, y, w, h)),
    b: T.b.map(([t, x, y, w, h, d, m, v, f, pp]) => [t, ...rr(x, y, w, h), (d || []).map(([dx, dy]) => [H0 - 1 - dy, dx]), m ? rotMask(m, w, h) : null, v && fxFind(t, v[0], v[1], v[2]) ? [v[0], v[1], (v[2] + 1) % (fxFind(t, v[0], v[1], v[2]).R + 1)] : null, f?.length ? fRot(t, f, H0) : null, pp || null]) };
}
const entryCells = (px, py, e) => maskCells(px + e[1], py + e[2], e[3], e[4], e[6]);
function tplOk(T, px, py) {
  if (px < 0 || py < 0 || px + T.w > W || py + T.h > H) return false;
  return T.b.every(e => fitsCells(e[0], entryCells(px, py, e)) && doorsFree((e[5] || []).map(([dx, dy]) => (py + dy) * W + px + dx)));
}
// Stempeln über vorhandenen Gebäuden (seit Version 34): je Gebäude der Vorlage neu, schon da (gleicher Typ, gleiche Fläche) oder belegt.
// Gesetzt wird nur, was frei ist; nichts Vorhandenes wird ersetzt. So lässt sich ein Blueprint aus dem Spiel an den eigenen Gebäuden ausrichten.
function tplFit(T, px, py) {
  return T.b.map(e => {
    const c = entryCells(px, py, e); if (!c) return 'out';
    const u = occ[c[0]], o = u ? blds.get(u) : null;
    if (o && o.t === e[0] && o.cells.length === c.length && c.every(k => o._set.has(k))) return 'same';
    return BT.has(e[0]) && fitsCells(e[0], c) && doorsFree((e[5] || []).map(([dx, dy]) => (py + dy) * W + px + dx)) ? 'new' : 'clash';
  });
}
function tplPut(T, px, py, keep = false) {
  let miss = 0;
  const st = keep ? tplFit(T, px, py) : null, cnt = { new: 0, same: 0, clash: 0, out: 0 };
  for (const [v, x, y, w, h] of T.ter) for (let j = py + y; j < py + y + h; j++) for (let i = px + x; i < px + x + w; i++) { if (!inMap(i, j)) continue; const k = j * W + i; if (!occ[k] && !wcnt[k] && (!keep || !terr[k])) terr[k] = v; }
  for (const [x, y, w, h] of T.cl || []) for (let j = py + y; j < py + y + h; j++) for (let i = px + x; i < px + x + w; i++) { if (!inMap(i, j)) continue; const k = j * W + i; if (ceilOk(k)) ceil[k] = 1; }
  T.b.forEach((e, n) => {
    if (st) { cnt[st[n]]++; if (st[n] !== 'new') return; }
    const c = entryCells(px, py, e);
    if (BT.has(e[0]) && fitsCells(e[0], c)) { const o = addB(e[0], c, (e[5] || []).map(([dx, dy]) => (py + dy) * W + px + dx), e[7] || null); if (e[8]?.length) { o.f = fAbs(e[8], px, py); fKeep(o); } if (e[9]) o.p = { ...e[9] }; } else miss++;
  });
  if (st) { cnt.clash += miss; cnt.new -= miss; return cnt; }
  return miss;
}
function captureTpl(r) {
  const ter = [];
  for (let y = r.y; y < r.y + r.h; y++) { let x = r.x; while (x < r.x + r.w) { const k = y * W + x, v = terr[k]; if (!v || wcnt[k]) { x++; continue; } let e = x; while (e < r.x + r.w && terr[y * W + e] === v && !wcnt[y * W + e]) e++; ter.push([v, x - r.x, y - r.y, e - x, 1]); x = e; } }
  const cl = [];
  for (let y = r.y; y < r.y + r.h; y++) { let x = r.x; while (x < r.x + r.w) { if (!ceil[y * W + x] || !ceilOk(y * W + x)) { x++; continue; } let e = x; while (e < r.x + r.w && ceil[y * W + e] && ceilOk(y * W + e)) e++; cl.push([x - r.x, y - r.y, e - x, 1]); x = e; } }
  const b = [];
  for (const o of blds.values()) { const q = outerOf(o); if (q.x >= r.x && q.y >= r.y && q.x + q.w <= r.x + r.w && q.y + q.h <= r.y + r.h) b.push([o.t, o.x - r.x, o.y - r.y, o.w, o.h, doorXY(o).map(([x, y]) => [x - r.x, y - r.y]), maskOf(o), o.v || null, o.f?.length ? fRel(o, r.x, r.y) : null, o.p || null]); }
  return { w: r.w, h: r.h, ter, cl, b };
}

// ---------- Mehrfachauswahl ----------
// msel: { us: Gebäude-uids, tt: freie Kacheln mit Straße, Mauer oder Decke }. Verschieben und Drehen laufen über eine
// Vorlage aus der Auswahl: alles herausnehmen, gedreht an der neuen Stelle stempeln, ein Rückgängig-Schritt.
let msel = null;
const ttHas = k => (terr[k] && !wcnt[k] && !occ[k]) || (ceil[k] && ceilOk(k));
const mselOn = () => !!msel && msel.us.size + msel.tt.size > 0;
function mselBlds() { return msel ? [...msel.us].map(u => blds.get(u)).filter(Boolean) : []; }
function setMsel(us, tt) {
  for (const u of [...us]) if (!blds.has(u)) us.delete(u);
  for (const k of [...tt]) if (!ttHas(k)) tt.delete(k);
  if (!us.size && !tt.size) { msel = null; selU = 0; }
  else if (us.size === 1 && !tt.size) { msel = null; selU = [...us][0]; }
  else { msel = { us, tt }; selU = 0; }
  computeSelReach(); refreshPanels(); schedule();
}
function mselBase() { return { us: new Set(msel ? msel.us : (selU ? [selU] : [])), tt: new Set(msel ? msel.tt : []) }; }
function mselFromRect(r, add) {
  const { us, tt } = add ? mselBase() : { us: new Set(), tt: new Set() };
  for (const o of blds.values()) { const q = outerOf(o); if (q.x >= r.x && q.y >= r.y && q.x + q.w <= r.x + r.w && q.y + q.h <= r.y + r.h) us.add(o.u); }
  for (let y = r.y; y < r.y + r.h; y++) for (let x = r.x; x < r.x + r.w; x++) if (ttHas(y * W + x)) tt.add(y * W + x);
  setMsel(us, tt);
}
function mselToggle(u) { const { us, tt } = mselBase(); if (us.has(u)) us.delete(u); else us.add(u); setMsel(us, tt); }
function mselTpl() {
  const bs = mselBlds(), tt = [...msel.tt].filter(ttHas);
  let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
  const grow = (x, y, w, h) => { x0 = Math.min(x0, x); y0 = Math.min(y0, y); x1 = Math.max(x1, x + w); y1 = Math.max(y1, y + h); };
  for (const o of bs) { const q = outerOf(o); grow(q.x, q.y, q.w, q.h); }
  for (const k of tt) grow(k % W, (k / W) | 0, 1, 1);
  const B = { x: x0, y: y0, w: x1 - x0, h: y1 - y0 }, ter = [], cl = [], rows = new Map();
  for (const k of tt) { const y = (k / W) | 0; if (!rows.has(y)) rows.set(y, []); rows.get(y).push(k % W); }
  for (const [y, xs] of rows) {
    xs.sort((a, b) => a - b);
    const tv = x => { const k = y * W + x; return !wcnt[k] && !occ[k] ? terr[k] : 0; }, cv1 = x => ceil[y * W + x] && ceilOk(y * W + x) ? 1 : 0;
    for (const [get, out] of [[tv, ter], [cv1, cl]]) {
      let i = 0;
      while (i < xs.length) { const v = get(xs[i]); if (!v) { i++; continue; } let e = i; while (e + 1 < xs.length && xs[e + 1] === xs[e] + 1 && get(xs[e + 1]) === v) e++; const run = [xs[i] - B.x, y - B.y, e - i + 1, 1]; out.push(out === ter ? [v, ...run] : run); i = e + 1; }
    }
  }
  const b = bs.map(o => [o.t, o.x - B.x, o.y - B.y, o.w, o.h, doorXY(o).map(([x, y]) => [x - B.x, y - B.y]), maskOf(o), o.v || null, o.f?.length ? fRel(o, B.x, B.y) : null, o.p || null]);
  return { T: { w: B.w, h: B.h, ter, cl, b }, B };
}
// n Vierteldrehungen im Uhrzeigersinn um die Mitte des Auswahlrahmens, dann um dx, dy verschieben
function mselPlace(base, n, dx, dy) {
  let R = base.T; for (let i = 0; i < n % 4; i++) R = rotTpl(R);
  const odd = n % 2 === 1, B = base.B;
  return { R, nx: B.x + (odd ? Math.floor((B.w - B.h) / 2) : 0) + dx, ny: B.y + (odd ? Math.floor((B.h - B.w) / 2) : 0) + dy };
}
function mselCheck(R, nx, ny) {
  if (nx < 0 || ny < 0 || nx + R.w > W || ny + R.h > H) return 'The selection would stick out over the map edge there.';
  const ign = mselBlds();
  for (const e of R.b) { const c = entryCells(nx, ny, e); if (!c || !fitsCells(e[0], c, ign) || !doorsFree((e[5] || []).map(([x, y]) => (ny + y) * W + nx + x), ign)) return 'There is no room for all buildings of the selection. Rooms may only touch at the wall, houses also directly, but not in front of an entrance.'; }
  return null;
}
function mselShapes(R, nx, ny) { const out = []; for (const e of R.b) { const c = entryCells(nx, ny, e); if (c) out.push(tmpShape(e[0], c, (e[5] || []).map(([dx, dy]) => [nx + dx, ny + dy]), e[7] || null)); } return out; }
function mselApply(n, dx, dy, base = mselTpl()) {
  if (!mselOn() || (!(n % 4) && !dx && !dy)) return false;
  const { R, nx, ny } = mselPlace(base, n, dx, dy), err = mselCheck(R, nx, ny);
  if (err) { toast(err); return false; }
  const s = snap(), bs = mselBlds(), fBefore = bs.reduce((a, o) => a + (o.f?.length || 0), 0);
  for (const o of bs) liftB(o);
  for (const k of msel.tt) { if (!wcnt[k] && !occ[k]) terr[k] = 0; ceil[k] = 0; }
  let lost = 0;
  for (const [, x, y, w, h] of R.ter) for (let j = ny + y; j < ny + y + h; j++) for (let i = nx + x; i < nx + x + w; i++) if (occ[j * W + i] || wcnt[j * W + i]) lost++;
  const u0 = nextU, miss = tplPut(R, nx, ny);
  if (miss) { restore(s); toast('There is no room for all buildings of the selection.'); return false; }
  undoS.push(s); while (undoS.length > undoCap()) undoS.shift(); redoS.length = 0;
  const us = new Set([...blds.keys()].filter(u => u >= u0)), tt = new Set();
  for (const [, x, y, w, h] of R.ter) for (let j = ny + y; j < ny + y + h; j++) for (let i = nx + x; i < nx + x + w; i++) tt.add(j * W + i);
  for (const [x, y, w, h] of R.cl) for (let j = ny + y; j < ny + y + h; j++) for (let i = nx + x; i < nx + x + w; i++) tt.add(j * W + i);
  const fAfter = [...us].reduce((a, u) => a + (blds.get(u).f?.length || 0), 0), msg = [];
  if (fAfter < fBefore) msg.push(`${fBefore - fAfter} furniture could not be rotated along.`);
  if (lost) msg.push(`${lost} road or wall tiles lay under other buildings and were dropped.`);
  if (msg.length) toast(msg.join(' '));
  dirty(); setMsel(us, tt); return true;
}
function mselDelete() {
  if (!mselOn()) return; commit();
  for (const o of mselBlds()) liftB(o);
  for (const k of msel.tt) { if (!wcnt[k] && !occ[k]) terr[k] = 0; ceil[k] = 0; }
  msel = null; selU = 0; selReach = null; dirty();
}
// Pfeiltasten und R wirken auch auf ein einzeln ausgewähltes Gebäude
function groupStep(n, dx, dy) {
  const tmp = !msel && selU; if (tmp) msel = { us: new Set([selU]), tt: new Set() };
  const ok = mselApply(n, dx, dy); if (!ok && tmp) msel = null; return ok;
}

// ---------- background layers ----------
const KINDS = { map:'Map', soil:'Soil', moist:'Moisture', custom:'Custom' };
let layers = [], actLayer = null, idb = null;
function idbOpen() { return new Promise(res => { try { const r = indexedDB.open('syx-bezirksplaner', 1); r.onupgradeneeded = () => r.result.createObjectStore('layers', { keyPath: 'id' }); r.onsuccess = () => res(r.result); r.onerror = () => res(null); r.onblocked = () => res(null); } catch { res(null); } }); }
function idbPut(L) { if (!idb) return; try { idb.transaction('layers', 'readwrite').objectStore('layers').put({ id: L.id, kind: L.kind, blob: L.blob, vis: L.vis, op: L.op, x: L.x, y: L.y, ppt: L.ppt, ord: L.ord }); } catch { /* Speicher blockiert */ } }
function idbDel(id) { if (!idb) return; try { idb.transaction('layers', 'readwrite').objectStore('layers').delete(id); } catch { /* Speicher blockiert */ } }
function idbAll() { return new Promise(res => { if (!idb) return res([]); try { const r = idb.transaction('layers').objectStore('layers').getAll(); r.onsuccess = () => res(r.result || []); r.onerror = () => res([]); } catch { res([]); } }); }
function makeLayer(rec) {
  const L = { ...rec, url: URL.createObjectURL(rec.blob), img: new Image() };
  L.img.onload = () => {
    if (!L.ppt) {
      const nw = L.img.naturalWidth, nh = L.img.naturalHeight;
      if (nw === nh && nw % 768 === 0 && nw <= 6144) { L.ppt = nw / 768; L.x = 0; L.y = 0; toast(`Recognised as a super screenshot: ${nw / 768} pixels per tile, map 768 × 768. Use “Use map size” to adjust the plan.`); }
      else L.ppt = nw / W;
      idbPut(L);
    }
    needBase = true; refreshLayers(); schedule();
  };
  L.img.src = L.url; return L;
}
function addLayerFiles(files) {
  let n = 0;
  for (const f of files) {
    if (!f.type.startsWith('image/')) continue;
    const nm = f.name.toLowerCase();
    const kind = /soil|fert|boden/.test(nm) ? 'soil' : /moist|feucht|water/.test(nm) ? 'moist' : layers.some(l => l.kind === 'map') ? 'custom' : 'map';
    const L = makeLayer({ id: 'L' + Date.now() + '_' + n, kind, blob: f, vis: true, op: kind === 'map' ? 1 : 0.55, x: 0, y: 0, ppt: 0, ord: layers.length ? Math.max(...layers.map(l => l.ord)) + 1 : 0 });
    layers.push(L); actLayer = L.id; idbPut(L); n++;
  }
  if (n) { toast(n === 1 ? 'Layer added. Fine-tune it with “Align”.' : `${n} layers added.`); refreshLayers(); schedule(); }
  else toast('Please choose an image file (PNG or JPG).');
}

// ---------- render ----------
const cv = document.getElementById('cv'), ctx = cv.getContext('2d');
const stage = document.getElementById('stage');
let z = 8, ox = 0, oy = 0, dpr = 1, vw = 0, vh = 0;
const baseC = document.createElement('canvas'), baseX = baseC.getContext('2d');
const ovC = document.createElement('canvas'), ovX = ovC.getContext('2d');
let needBase = true, needOv = true, raf = 0;
function dirty() { gen++; needBase = true; needOv = true; reachDirty = true; loadStale = true; computeSelReach(); schedule(); refreshPanels(); autosave(); }
function schedule() { if (!raf) raf = requestAnimationFrame(draw); }
function resize() { dpr = window.devicePixelRatio || 1; const r = stage.getBoundingClientRect(); vw = r.width; vh = r.height; cv.width = Math.max(1, Math.round(vw * dpr)); cv.height = Math.max(1, Math.round(vh * dpr)); schedule(); }
function fit() { const m = 40; z = Math.max(0.5, Math.min(32, Math.min((vw - m) / W, (vh - m) / H))); ox = (vw - W * z) / 2; oy = (vh - H * z) / 2; schedule(); }
const COL_GROUND = [26, 33, 40], COL_ROAD = [92, 84, 70], COL_WALL = [58, 62, 68], COL_RING = [84, 88, 96], COL_DOOR = [200, 160, 70], COL_CEIL = [128, 92, 58], COL_CEIL_ROAD = [150, 118, 80];
const anyLayer = () => layers.some(l => l.vis && l.img.complete && l.img.naturalWidth);
function paintBase() {
  baseC.width = W; baseC.height = H; const im = baseX.createImageData(W, H), d = im.data, see = anyLayer();
  for (let i = 0; i < W * H; i++) {
    const k = i * 4;
    if (wcnt[i]) { const c = dcnt[i] ? COL_DOOR : COL_RING; d[k] = c[0]; d[k + 1] = c[1]; d[k + 2] = c[2]; d[k + 3] = 255; continue; }
    const t = terr[i];
    if (ceil[i]) { const c = t === 1 ? COL_CEIL_ROAD : COL_CEIL; d[k] = c[0]; d[k + 1] = c[1]; d[k + 2] = c[2]; d[k + 3] = see ? 220 : 255; continue; }
    if (!t && see) { d[k + 3] = 0; continue; }
    const c = t === 1 ? COL_ROAD : t === 2 ? COL_WALL : COL_GROUND, chk = !t && (((i % W) + ((i / W) | 0)) & 1) ? 3 : 0;
    d[k] = c[0] + chk; d[k + 1] = c[1] + chk; d[k + 2] = c[2] + chk; d[k + 3] = see && t === 1 ? 210 : 255;
  }
  baseX.putImageData(im, 0, 0); needBase = false;
}
function hexRgb(h) { const n = parseInt(h.slice(1), 16); return [n >> 16 & 255, n >> 8 & 255, n & 255]; }
const RG_GOOD = hexRgb(GOOD), RG_WARN = hexRgb(WARN), RG_BAD = hexRgb(BAD), RG_GOLD = hexRgb(GOLD);
function paintOv() {
  ovC.width = W; ovC.height = H; needOv = false;
  if (ovMode === 'off') return;
  if (OV2.includes(ovMode)) { paintOv2(); return; }
  const im = ovX.createImageData(W, H), d = im.data, see = anyLayer();
  const put = (i, c, a) => { const k4 = i * 4; d[k4] = c[0]; d[k4 + 1] = c[1]; d[k4 + 2] = c[2]; d[k4 + 3] = see ? a * .55 : a; };
  if (ovMode === 'load') {
    if (!load) computeLoad();
    const act = GROUPS.filter(g => groupOn[g.k]);
    load.houses.forEach((h, hi) => {
      if (blds.get(h.u) !== h) return;
      let st = 0; for (const g of act) { const u = load.per[g.k].who[hi]; if (!u) { st = 3; break; } st = Math.max(st, loadState(g, u)); }
      const c = st === 3 ? RG_BAD : st >= 1 ? RG_WARN : RG_GOOD; for (const cc of h.cells) put(cc, c, st ? 130 : 90);
    });
    for (const g of act) {
      const byB = load.per[g.k].byB, cap = capOf(g), mx = Math.max(1, ...byB.values());
      for (const [u, v] of byB) { const b = blds.get(u); if (!b) continue; let c, a; if (cap) { const s = loadState(g, u); c = s === 2 ? RG_BAD : s === 1 ? RG_WARN : RG_GOOD; a = 150; } else { c = RG_GOLD; a = 40 + Math.round(v / mx * 150); } for (const cc of b.cells) put(cc, c, a); }
    }
    ovX.putImageData(im, 0, 0); return;
  }
  if (reachDirty) computeReach();
  const act = GROUPS.filter(g => groupOn[g.k]), dg = GROUPS.find(g => g.k === distGroup), dR = groupMaxR(dg);
  for (let i = 0; i < W * H; i++) {
    if (!walkable(i) || occ[i]) continue;
    if (ovMode === 'cov') {
      if (!act.length) continue;
      let k = 0; for (const g of act) if (groupDistAt(g, i) !== 65535) k++;
      put(i, k === act.length ? RG_GOOD : k === 0 ? RG_BAD : RG_WARN, k === act.length ? 70 : 115);
    } else {
      const dd = groupDistAt(dg, i);
      if (dd === 65535) put(i, RG_BAD, 95); else { const f = dd / dR; put(i, f < .5 ? RG_GOOD : f < .8 ? RG_WARN : [230, 120, 60], 60 + Math.round(f * 70)); }
    }
  }
  ovX.putImageData(im, 0, 0);
}
let preview = null, selReach = null;
function cellRuns(cells, f) { let s = -1, p = -2; for (const c of cells) { if (c === p + 1 && ((c % W) !== 0)) { p = c; continue; } if (s >= 0) f(s, p); s = c; p = c; } if (s >= 0) f(s, p); }
function drawBld(o, alpha = 1, ring = false) {
  const b = BT.get(o.t), col = CAT_COL[b?.c] || '#888';
  if (ring && o._ring.size) { ctx.fillStyle = `rgb(${COL_RING})`; ctx.globalAlpha = alpha * .9; for (const k of o._ring) ctx.fillRect(ox + (k % W) * z, oy + ((k / W) | 0) * z, z, z); }
  const fill = (style, a) => { ctx.fillStyle = style; ctx.globalAlpha = alpha * a; cellRuns(o.cells, (s, e) => { const y = (s / W) | 0; ctx.fillRect(ox + (s % W) * z, oy + y * z, (e - s + 1) * z, z); }); };
  if (!b?.o) fill('rgb(20,26,32)', .55);
  fill(col, b?.o ? .18 : .32); ctx.globalAlpha = alpha;
  if (z >= 3 && o.f?.length) { const fu = furnOf(o.t); if (fu) { const n = fu.fs.groups.length; ctx.globalAlpha = alpha * .8; for (const p of o.f) for (const [x, y, k] of fCells(fu.fs, p)) { ctx.fillStyle = `hsl(${Math.round((p[0] * 360 / Math.max(1, n)) + 35) % 360} 45% ${blocks(fu.fs, k) ? 38 : 24}%)`; ctx.fillRect(ox + x * z + .5, oy + y * z + .5, z - 1, z - 1); } ctx.globalAlpha = alpha; } }
  if (z >= 5 && b?.fx) { const v = fxOf(o); if (v) { ctx.fillStyle = col; ctx.globalAlpha = alpha * .5; const m = Math.max(1, z * .18); for (let y = 0; y < v.h; y++) for (let x = 0; x < v.w; x++) { const ch = v.grid[y][x]; if (ch === 'S' || ch === '#') ctx.fillRect(ox + (o.x + x) * z + m, oy + (o.y + y) * z + m, z - 2 * m, z - 2 * m); } ctx.globalAlpha = alpha; } }
  if (b?.o && z >= 4) { ctx.strokeStyle = col; ctx.globalAlpha = alpha * .22; ctx.lineWidth = 1; ctx.beginPath(); cellRuns(o.cells, (s, e) => { const y = (s / W) | 0; if (y % 2) return; ctx.moveTo(ox + (s % W) * z + 2, oy + y * z + z / 2); ctx.lineTo(ox + (e % W + 1) * z - 2, oy + y * z + z / 2); }); ctx.stroke(); ctx.globalAlpha = alpha; }
  ctx.strokeStyle = col; ctx.lineWidth = Math.max(1, Math.min(2, z / 6)); ctx.beginPath();
  for (const c of o.cells) {
    const x = c % W, y = (c / W) | 0, px = ox + x * z, py = oy + y * z;
    if (!o._set.has(c - W) || y === 0) { ctx.moveTo(px, py); ctx.lineTo(px + z, py); }
    if (!o._set.has(c + W) || y === H - 1) { ctx.moveTo(px, py + z); ctx.lineTo(px + z, py + z); }
    if (x === 0 || !o._set.has(c - 1)) { ctx.moveTo(px, py); ctx.lineTo(px, py + z); }
    if (x === W - 1 || !o._set.has(c + 1)) { ctx.moveTo(px + z, py); ctx.lineTo(px + z, py + z); }
  }
  ctx.stroke();
  const px = ox + o.x * z, py = oy + o.y * z, pw = o.w * z, ph = o.h * z;
  const im = imgs.get(o.t), s = Math.min(pw, ph); let ty = py + ph / 2, hasIcon = false;
  if (im && im.complete && s >= 26) { const is = Math.min(32, Math.floor(s * .45)); ctx.drawImage(im, px + pw / 2 - is / 2, py + ph / 2 - is / 2 - (ph > 52 ? 9 : 0), is, is); ty = py + ph / 2 + is / 2 + 4; hasIcon = true; }
  if (pw >= 40 && ph >= 18 && (ph >= 52 || !hasIcon)) {
    ctx.fillStyle = '#e2ddd0'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
    const fs = Math.max(9, Math.min(13, z * 1.1)); ctx.font = `${fs}px "Segoe UI", system-ui, sans-serif`;
    ctx.fillText(fitText(b?.n || o.t, pw - 6), px + pw / 2, Math.min(ty + 4, py + ph - fs * 1.6));
    ctx.fillStyle = '#9a8e80'; ctx.font = `${fs - 1}px Consolas, monospace`; ctx.fillText(isRect(o) ? `${o.w}×${o.h}` : `${o.cells.length} K.`, px + pw / 2, Math.min(ty + 4 + fs + 2, py + ph - fs * .6));
  }
  ctx.globalAlpha = 1;
}
function badge(text, cx, cy, col) {
  ctx.font = '11px Consolas, monospace'; const tw = ctx.measureText(text).width + 8;
  ctx.fillStyle = 'rgba(12,16,20,0.88)'; ctx.fillRect(cx - tw / 2, cy - 8, tw, 16); ctx.strokeStyle = col; ctx.lineWidth = 1; ctx.strokeRect(cx - tw / 2 + .5, cy - 7.5, tw - 1, 15);
  ctx.fillStyle = '#f2ece0'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillText(text, cx, cy + .5);
}
function draw() {
  raf = 0; const zt = `${z >= 10 ? Math.round(z) : z.toFixed(1)} px`; if (zValEl.value !== zt) zValEl.value = zt;
  if (needBase) paintBase();
  if (needOv) paintOv();
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.fillStyle = '#080b0e'; ctx.fillRect(0, 0, vw, vh);
  ctx.fillStyle = `rgb(${COL_GROUND})`; ctx.fillRect(ox, oy, W * z, H * z);
  ctx.save(); ctx.beginPath(); ctx.rect(ox, oy, W * z, H * z); ctx.clip();
  for (const L of [...layers].sort((a, b) => a.ord - b.ord)) {
    if (!L.vis || !L.img.complete || !L.img.naturalWidth || !L.ppt) continue;
    ctx.globalAlpha = L.op; ctx.imageSmoothingEnabled = z / L.ppt < 1;
    ctx.drawImage(L.img, ox + L.x * z, oy + L.y * z, L.img.naturalWidth / L.ppt * z, L.img.naturalHeight / L.ppt * z);
  }
  ctx.restore(); ctx.globalAlpha = 1; ctx.imageSmoothingEnabled = false;
  ctx.drawImage(baseC, ox, oy, W * z, H * z);
  const x0 = Math.max(0, Math.floor(-ox / z)), x1 = Math.min(W, Math.ceil((vw - ox) / z));
  const y0 = Math.max(0, Math.floor(-oy / z)), y1 = Math.min(H, Math.ceil((vh - oy) / z));
  ctx.lineWidth = 1;
  if (z >= 6) {
    ctx.strokeStyle = anyLayer() ? 'rgba(0,0,0,0.2)' : 'rgba(140,150,160,0.07)'; ctx.beginPath();
    for (let x = x0; x <= x1; x++) { const px = Math.round(ox + x * z) + .5; ctx.moveTo(px, oy + y0 * z); ctx.lineTo(px, oy + y1 * z); }
    for (let y = y0; y <= y1; y++) { const py = Math.round(oy + y * z) + .5; ctx.moveTo(ox + x0 * z, py); ctx.lineTo(ox + x1 * z, py); }
    ctx.stroke();
  }
  ctx.strokeStyle = 'rgba(224,170,56,0.22)'; ctx.beginPath();
  for (let x = Math.ceil(x0 / 10) * 10; x <= x1; x += 10) { const px = Math.round(ox + x * z) + .5; ctx.moveTo(px, oy + y0 * z); ctx.lineTo(px, oy + y1 * z); }
  for (let y = Math.ceil(y0 / 10) * 10; y <= y1; y += 10) { const py = Math.round(oy + y * z) + .5; ctx.moveTo(ox + x0 * z, py); ctx.lineTo(ox + x1 * z, py); }
  ctx.stroke();
  if (z >= 6) { ctx.strokeStyle = 'rgba(40,26,14,0.55)'; ctx.lineWidth = 1; ctx.beginPath(); for (let y = y0; y < y1; y++) for (let x = x0; x < x1; x++) if (ceil[y * W + x]) { const px = ox + x * z, py = oy + y * z; ctx.moveTo(px + 1, py + z - 1); ctx.lineTo(px + z - 1, py + 1); } ctx.stroke(); }
  const vis = o => { const q = outerOf(o); return !(q.x > x1 || q.y > y1 || q.x + q.w < x0 || q.y + q.h < y0); };
  for (const o of blds.values()) if (vis(o)) drawBld(o);
  ctx.strokeStyle = BAD; ctx.lineWidth = 2; ctx.setLineDash([4, 3]);
  for (const o of blds.values()) { if (!vis(o)) continue; if (isFixed(o.t) && (!fxOf(o) || entBlocked(o))) ctx.strokeRect(ox + o.x * z + 1, oy + o.y * z + 1, o.w * z - 2, o.h * z - 2); }
  ctx.setLineDash([]);
  if (ovMode !== 'off' && ovC.width) ctx.drawImage(ovC, ox, oy, W * z, H * z);
  if (ovMode === 'load' && load) {
    for (const g of GROUPS.filter(g => groupOn[g.k])) {
      const cap = capOf(g);
      for (const [u, v] of load.per[g.k].byB) { const b = blds.get(u); if (!b || !vis(b) || Math.min(b.w, b.h) * z < 14) continue; const s = loadState(g, u); badge(cap ? `${Math.round(v)}/${cap}` : `${Math.round(v)} E.`, ox + (b.x + b.w / 2) * z, oy + (b.y + b.h / 2) * z, cap ? (s === 2 ? BAD : s === 1 ? WARN : GOOD) : GOLD); }
    }
  }
  const sel = blds.get(selU);
  if (sel) {
    if (selReach && ovMode !== 'load') { ctx.fillStyle = 'rgba(224,170,56,0.10)'; for (let y = y0; y < y1; y++) for (let x = x0; x < x1; x++) if (selReach[y * W + x] !== 65535) ctx.fillRect(ox + x * z, oy + y * z, z, z); }
    const q = outerOf(sel); ctx.strokeStyle = GOLD; ctx.lineWidth = 2; ctx.setLineDash([5, 3]); ctx.strokeRect(ox + q.x * z - 1, oy + q.y * z - 1, q.w * z + 2, q.h * z + 2); ctx.setLineDash([]);
  }
  if (msel) {
    ctx.fillStyle = 'rgba(224,170,56,0.22)';
    for (const k of msel.tt) { const x = k % W, y = (k / W) | 0; if (x >= x0 && x < x1 && y >= y0 && y < y1) ctx.fillRect(ox + x * z, oy + y * z, z, z); }
    ctx.strokeStyle = GOLD; ctx.lineWidth = 2; ctx.setLineDash([5, 3]);
    for (const o of mselBlds()) { if (!vis(o)) continue; const q = outerOf(o); ctx.strokeRect(ox + q.x * z - 1, oy + q.y * z - 1, q.w * z + 2, q.h * z + 2); }
    ctx.setLineDash([]);
  }
  if (preview) drawPreview(preview);
  ctx.strokeStyle = 'rgba(180,150,85,0.55)'; ctx.lineWidth = 1; ctx.strokeRect(Math.round(ox) - .5, Math.round(oy) - .5, Math.round(W * z) + 1, Math.round(H * z) + 1);
  ctx.fillStyle = '#9a8e80'; ctx.font = '10px Consolas, monospace'; ctx.textBaseline = 'bottom'; ctx.textAlign = 'center';
  const step = z >= 4 ? 10 : z >= 2 ? 20 : z >= 1 ? 50 : 100;
  for (let x = Math.ceil(x0 / step) * step; x <= x1; x += step) if (oy > 14) ctx.fillText(String(x), ox + x * z, oy - 3);
  ctx.textAlign = 'right'; ctx.textBaseline = 'middle';
  for (let y = Math.ceil(y0 / step) * step; y <= y1; y += step) if (ox > 22) ctx.fillText(String(y), ox - 4, oy + y * z);
}
function drawPreview(p) {
  const okC = p.ok ? GOLD : BAD;
  if (p.kind === 'tpl') {
    ctx.fillStyle = p.ok ? 'rgba(224,170,56,0.08)' : 'rgba(208,90,72,0.2)'; ctx.fillRect(ox + p.x * z, oy + p.y * z, p.w * z, p.h * z);
    for (const [v, x, y, w, h] of p.T.ter) { ctx.fillStyle = v === 1 ? 'rgba(160,140,100,0.55)' : 'rgba(110,115,122,0.85)'; ctx.fillRect(ox + (p.x + x) * z, oy + (p.y + y) * z, w * z, h * z); }
    for (const [x, y, w, h] of p.T.cl || []) { ctx.fillStyle = `rgba(${COL_CEIL},0.8)`; ctx.fillRect(ox + (p.x + x) * z, oy + (p.y + y) * z, w * z, h * z); }
    for (const o of p.shapes) { drawBld(o, o._clash ? .35 : .9, true); if (o._clash) { ctx.fillStyle = 'rgba(208,90,72,0.45)'; for (const c of o.cells) ctx.fillRect(ox + (c % W) * z, oy + ((c / W) | 0) * z, z, z); } }
    for (const o of p.shapes) if (!o._clash) for (const [dx, dy] of o._doors) { ctx.fillStyle = `rgba(${COL_DOOR},0.95)`; ctx.fillRect(ox + dx * z, oy + dy * z, z, z); }
  } else if (p.shape) {
    drawBld(p.shape, .85, true);
    for (const [dx, dy] of p.shape._doors || []) { ctx.fillStyle = `rgba(${COL_DOOR},0.95)`; ctx.fillRect(ox + dx * z, oy + dy * z, z, z); }
    if (!p.ok) { ctx.fillStyle = 'rgba(208,90,72,0.35)'; ctx.fillRect(ox + p.x * z, oy + p.y * z, p.w * z, p.h * z); }
  } else {
    ctx.fillStyle = p.ok ? (p.kind === 'erase' ? 'rgba(208,90,72,0.22)' : p.kind === 'cap' || p.kind === 'msel' ? 'rgba(120,170,220,0.15)' : 'rgba(224,170,56,0.22)') : 'rgba(208,90,72,0.35)';
    ctx.fillRect(ox + p.x * z, oy + p.y * z, p.w * z, p.h * z);
  }
  ctx.strokeStyle = okC; ctx.lineWidth = 1.5; ctx.strokeRect(ox + p.x * z + .5, oy + p.y * z + .5, p.w * z - 1, p.h * z - 1);
  if (p.label) {
    ctx.font = '12px Consolas, monospace'; const tw = ctx.measureText(p.label).width + 12;
    let lx = ox + (p.x + p.w) * z + 8, ly = oy + p.y * z - 24; if (ly < 4) ly = oy + (p.y + p.h) * z + 8; if (lx + tw > vw - 4) lx = Math.max(4, vw - tw - 4);
    ctx.fillStyle = 'rgba(12,16,20,0.92)'; ctx.fillRect(lx, ly, tw, 18); ctx.strokeStyle = okC; ctx.lineWidth = 1; ctx.strokeRect(lx + .5, ly + .5, tw - 1, 17);
    ctx.fillStyle = '#f2ece0'; ctx.textAlign = 'left'; ctx.textBaseline = 'middle'; ctx.fillText(p.label, lx + 6, ly + 9.5);
  }
}
function fitText(s, w) { if (ctx.measureText(s).width <= w) return s; let t = s; while (t.length > 2 && ctx.measureText(t + '…').width > w) t = t.slice(0, -1); return t + '…'; }
function tmpShape(t, cells, doors = [], v = null) { const o = mkB({ u: -1, t, cells: [...cells], d: [], v }); o._doors = doors; return o; }

// ---------- tools & input ----------
const TOOLS = [
  { k:'sel', n:'Select', key:'Q', d:'M5 3l12 8-6 1-2 6z' },
  { k:'pan', n:'Pan', key:'Space', d:'M7 11V5a1.5 1.5 0 013 0v5M10 10V4a1.5 1.5 0 013 0v6M13 10V5.5a1.5 1.5 0 013 0V13c0 4-2.5 6-6 6s-5-2-6.5-5L4 11a1.5 1.5 0 012.6-1.4L7 11' },
  { k:'build', n:'Build', key:'B', d:'M3 9h18v11H3zM3 9l9-6 9 6M9 20v-6h6v6' },
  { k:'copy', n:'Copy', key:'V', d:'M8 8h11v11H8zM5 16V5h11' },
  { k:'stamp', n:'Stamp', key:'T', d:'M3 3h7v7H3zM14 3h7v7h-7zM3 14h7v7H3zM14 14h7v7h-7z' },
  { k:'cap', n:'Capture', key:'K', d:'M4 8V4h4M16 4h4v4M20 16v4h-4M8 20H4v-4M9 12h6M12 9v6' },
  { k:'exp', n:'Export', key:'X', d:'M12 15V3M7 8l5-5 5 5M4 14v6h16v-6' },
];
// Build group (Syx Pack v35): one tool in the rail, the modes sit in the strip on top of the map. 'clone' (stamp of one building) belongs to Room.
const BMODES = [
  { k:'bld', n:'Room', key:'D', d:'M3 9h18v11H3zM3 9l9-6 9 6M9 20v-6h6v6' },
  { k:'road', n:'Road', key:'S', d:'M7 3L4 21M17 3l3 18M12 4v3M12 10v3M12 16v3' },
  { k:'wall', n:'Wall', key:'M', d:'M3 6h18v12H3zM3 12h18M9 6v6M15 12v6M6 12v6M18 6v6' },
  { k:'door', n:'Door', key:'W', d:'M6 21V3h11v18M3 21h18M14 12h.01' },
  { k:'ceil', n:'Ceiling', key:'C', d:'M2 11l10-7 10 7M5 9v11M19 9v11M5 14h14' },
  { k:'erase', n:'Erase', key:'E', d:'M4 16l9-9 6 6-7 7H7zM10 20h10' },
];
const BUILD = new Set(['bld', 'road', 'wall', 'door', 'ceil', 'erase', 'clone']);
let lastBuild = 'bld';
const TOOL_NAME = { sel: 'Select', pan: 'Pan', bld: 'Build › Room', road: 'Build › Road', wall: 'Build › Wall', door: 'Build › Door', ceil: 'Build › Ceiling', erase: 'Build › Erase', clone: 'Build › Room (stamp)', copy: 'Copy', stamp: 'Stamp', cap: 'Capture', exp: 'Export', align: 'Align layer' };
const railEl = document.getElementById('rail');
const svgI = d => `<svg viewBox="0 0 24 24" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true"><path d="${d}"/></svg>`;
TOOLS.forEach((t, n) => {
  if (n === 2 || n === 3 || n === 6) { const d = document.createElement('div'); d.className = 'rdiv'; railEl.appendChild(d); }
  const b = document.createElement('button'); b.className = 'rt'; b.id = 'tool-' + t.k; b.title = `${t.n} (${t.key})`; b.setAttribute('aria-label', t.n);
  b.innerHTML = `${svgI(t.d)}<span>${t.n}</span><kbd>${t.key}</kbd>`;
  b.addEventListener('click', () => setTool(t.k === 'build' ? lastBuild : t.k)); railEl.appendChild(b);
});
const bModesEl = document.getElementById('bModes'), bOptsEl = document.getElementById('bOpts'), bStripEl = document.getElementById('bstrip');
for (const m of BMODES) {
  const b = document.createElement('button'); b.className = 'bmode'; b.id = 'bm-' + m.k; b.title = `${m.n} (${m.key})`;
  b.innerHTML = `${svgI(m.d)}${m.n}<kbd>${m.key}</kbd>`; b.addEventListener('click', () => setTool(m.k)); bModesEl.appendChild(b);
}
// Esc or right click without dragging: leave the tool, back to Select (as in the game)
function leaveTool() { setTool('sel'); preview = null; schedule(); }
function setTool(k) {
  if (k === 'build') k = lastBuild;
  if (k === 'align' && tool === 'align') k = prevTool && prevTool !== 'align' ? prevTool : 'sel';
  if (k === 'stamp' && !curTpl) curTpl = { T: BUILTIN[0], base: BUILTIN[0], rot: 0 };
  if (k === 'align' && !layers.length) { toast('Load a screenshot as a layer first (Views tab, Background layers).'); return; }
  if (k === 'align' && !actLayer) actLayer = layers[0].id;
  if (k === 'align' && tool !== 'align') prevTool = tool;
  if (BUILD.has(k)) lastBuild = k === 'clone' ? 'bld' : k;
  tool = k; if (k !== 'clone') stampT = null; if (k !== 'sel') msel = null; preview = null;
  for (const t of TOOLS) document.getElementById('tool-' + t.k).classList.toggle('on', t.k === k || (t.k === 'build' && BUILD.has(k)));
  for (const m of BMODES) document.getElementById('bm-' + m.k).classList.toggle('on', m.k === k || (k === 'clone' && m.k === 'bld'));
  cv.style.cursor = k === 'pan' || k === 'align' ? 'grab' : k === 'sel' ? 'default' : 'crosshair';
  updateHint(); refreshTpls(); refreshLayers(); schedule(); if (lastStatT) status(lastStatT);
}
// Options of the current build mode in the strip: building, shape, size (houses 1–9)
const FX_PICK_MAX = 9;
const fxPickN = (t, g) => { const n = BT.get(t).fx.G[g].I.length; return t === HOME_T ? Math.min(FX_PICK_MAX, n) : n; };
function stripOpts() {
  if (tool === 'clone' && stampT) { const b = BT.get(stampT.t); return `<span class="cur" title="Stamp of one building">${b?.i ? `<img src="${b.i}" alt="">` : ''}${esc(b?.n || stampT.t)}</span><span class="hs">stamp ${stampT.w} × ${stampT.h} · R rotates · Esc ends</span>`; }
  if (tool !== 'bld') return '';
  const b = BT.get(curType); if (!b) return '';
  let h = `<button class="cur" id="bCur" title="Choose another building (Buildings tab)">${b.i ? `<img src="${b.i}" alt="">` : ''}${esc(b.n)}</button>`;
  if (!b.fx) return h + `<span class="hs">${b.wl ? 'inner size · +1 tile wall ring' : 'no wall'}</span>`;
  const fx = b.fx, c = fxCurItem(curType), G = fx.G[c.g];
  if (fx.G.length > 1) h += `<span class="seg sm">${fx.G.map((_, g) => `<button data-fg="${g}" class="${g === c.g ? 'on' : ''}">${esc(fxGName(curType, g))}</button>`).join('')}</span>`;
  const n = fxPickN(curType, c.g);
  if (n > 1) {
    h += `<span class="vs"></span><span class="hs">${curType === HOME_T ? 'Houses' : 'Size'}</span>`;
    for (let s = 0; s < n; s++) { const it = G.I[s]; h += `<button class="num${s === c.s ? ' on' : ''}" data-fs="${s}" title="${esc(fxName(curType, fxFind(curType, c.g, s, 0)))}">${curType === HOME_T ? s + 1 : `${it[0].length}×${it.length}`}</button>`; }
  }
  return h + `<span class="vs"></span><span class="hs">${n > 1 ? 'E/Q ± · ' : ''}${c.R ? 'R rotates · ' : ''}click places</span>`;
}
function refreshStrip() {
  const on = BUILD.has(tool); bStripEl.hidden = !on; if (!on) return;
  const h = stripOpts(); bOptsEl.innerHTML = h; bOptsEl.hidden = !h; bStripEl.classList.toggle('has', !!h);
  bOptsEl.querySelectorAll('[data-fg]').forEach(x => x.addEventListener('click', () => { fxPickGroup(curType, +x.dataset.fg); updateHint(); if (lastT) fxPreview(lastT); }));
  bOptsEl.querySelectorAll('[data-fs]').forEach(x => x.addEventListener('click', () => { const c = fxCurItem(curType); fxCur[curType] = { g: c.g, s: +x.dataset.fs, r: c.r }; updateHint(); if (lastT) fxPreview(lastT); }));
  document.getElementById('bCur')?.addEventListener('click', () => { showLTab('b'); bSearch.focus(); });
}
function updateHint() {
  const b = BT.get(curType), bn = b?.n || curType;
  const M = {
    sel: msel ? 'Drag the selection to move it, arrow keys move 1 tile (Shift: 10), R rotates, Del deletes, Esc clears. Shift+click adds.' : 'Click a building, drag to move it. Drag a rectangle on empty ground to select an area, Shift+click adds buildings. Double-click furnishes, Ctrl+click picks it up as a stamp.',
    pan: 'Drag the map to move it.',
    bld: isFixed(curType) ? '' : 'Drag the inner size. Dragging into a room of the same type or its wall extends it, also to free shapes.',
    road: 'Road: drag a rectangle.', ceil: 'Ceiling: drag a rectangle. Works on free ground and roads, not on rooms, walls or free walls. Remove it with Erase (E).', wall: 'Free wall: drag a rectangle. For noise protection, lay a second row next to the wall ring.',
    door: 'Door: click a tile of the wall ring (not a corner). Click again to remove it.',
    erase: 'Erase: take tiles out of rooms. Erasing on the wall moves the wall inwards.',
    stamp: curTpl ? `${curTpl.T.n}, ${curTpl.T.w} × ${curTpl.T.h}: click to place, R rotates, Esc or right click ends.` : '',
    cap: 'Capture: drag an area. The form to save it appears in the Templates tab.',
    copy: 'Copy: drag an area, then stamp it right away. Buildings must lie inside the frame including their wall.',
    align: 'Align layer: drag the image with the mouse. Click “Align” again to finish.',
    exp: 'Export: drag the area that should go into the game. Buildings must lie inside the frame including their wall.',
    clone: '',
  };
  const ht = M[tool] || '', inB = BUILD.has(tool);
  document.getElementById('hint').textContent = inB ? '' : ht; const bh = document.getElementById('bHint'); bh.textContent = inB ? ht : ''; bh.hidden = !inB || !ht;
  refreshStrip();
}
function tileAt(e) { const r = cv.getBoundingClientRect(); return { x: Math.floor((e.clientX - r.left - ox) / z), y: Math.floor((e.clientY - r.top - oy) / z) }; }
let drag = null, spaceDown = false;
cv.addEventListener('contextmenu', e => e.preventDefault());
cv.addEventListener('dblclick', e => { if (tool !== 'sel') return; const u = pickAt(tileAt(e)), o = blds.get(u); if (o && canFurnish(o.t)) openFurnish(o); });
function pickAt(t) {
  if (!inMap(t.x, t.y)) return 0; const i = t.y * W + t.x;
  if (occ[i]) return occ[i];
  if (wcnt[i]) { const own = ownersOfRing(i); const s = own.find(o => o.u === selU); return (s || own[0])?.u || 0; }
  return 0;
}
function cloneFrom(o) {
  if (isFixed(o.t)) { const v = fxOf(o); if (v) fxCur[o.t] = { g: v.g, s: v.s, r: v.r }; curType = o.t; selU = 0; setTool('bld'); refreshPalette(); refreshPanels(); return; }
  stampT = { t: o.t, w: o.w, h: o.h, mask: maskOf(o), f: fRel(o, o.x, o.y), d: doorXY(o).map(([x, y]) => [x - o.x, y - o.y]) }; curType = o.t; setTool('clone'); refreshPalette();
}
cv.addEventListener('pointerdown', e => {
  cv.setPointerCapture(e.pointerId);
  const t = tileAt(e);
  if (e.button === 1 || e.button === 2 || tool === 'pan' || spaceDown) { drag = { kind: 'pan', sx: e.clientX, sy: e.clientY, ox, oy, rc: e.button === 2 }; cv.style.cursor = 'grabbing'; return; }
  if (e.button !== 0) return;
  if (tool === 'align') { const L = layers.find(l => l.id === actLayer); if (L) drag = { kind: 'layer', L, sx: e.clientX, sy: e.clientY, lx: L.x, ly: L.y }; return; }
  if ((tool === 'sel' || tool === 'bld') && (e.ctrlKey || e.metaKey)) { const u = pickAt(t); if (u) cloneFrom(blds.get(u)); return; }
  if (tool === 'sel') {
    const u = pickAt(t), k = inMap(t.x, t.y) ? t.y * W + t.x : -1;
    if (e.shiftKey) { if (u) mselToggle(u); else drag = { kind: 'msel', sx: t.x, sy: t.y, add: true }; schedule(); return; }
    if (msel && (msel.us.has(u) || (!u && msel.tt.has(k)))) { drag = { kind: 'gmove', sx: t.x, sy: t.y, moved: false, base: mselTpl() }; schedule(); return; }
    msel = null; selU = u; computeSelReach(); refreshPanels(); if (u) showRTab('sel');
    if (u) { const o = blds.get(u); drag = { kind: 'move', o, sx: t.x, sy: t.y, moved: false }; }
    else drag = { kind: 'msel', sx: t.x, sy: t.y, add: false };
    schedule(); return;
  }
  if (tool === 'clone') { placeClone(t); return; }
  if (tool === 'bld' && isFixed(curType)) { placeFx(t); return; }
  if (tool === 'stamp') { placeTpl(t); return; }
  if (tool === 'door') { toggleDoor(t); return; }
  if (['bld','road','wall','ceil','erase','cap','copy','exp'].includes(tool)) { drag = { kind: 'rect', sx: t.x, sy: t.y }; updateRectPreview(t); }
});
function movedCells(o, dx, dy) { const out = []; for (const c of o.cells) { const x = c % W + dx, y = ((c / W) | 0) + dy; if (!inMap(x, y)) return null; out.push(y * W + x); } return out; }
cv.addEventListener('pointermove', e => {
  const t = tileAt(e); status(t);
  if (drag?.kind === 'pan') { ox = drag.ox + e.clientX - drag.sx; oy = drag.oy + e.clientY - drag.sy; schedule(); return; }
  if (drag?.kind === 'layer') { const L = drag.L; L.x = Math.round((drag.lx + (e.clientX - drag.sx) / z) * 4) / 4; L.y = Math.round((drag.ly + (e.clientY - drag.sy) / z) * 4) / 4; schedule(); syncAlign(); return; }
  if (drag?.kind === 'move') {
    const o = drag.o, dx = t.x - drag.sx, dy = t.y - drag.sy;
    if (dx || dy) drag.moved = true;
    if (drag.moved) { const c = movedCells(o, dx, dy), ok = !!c && fitsCells(o.t, c, [o]) && doorsFree(o.d.map(i => i + dy * W + dx), [o]); preview = c ? { kind: 'move', shape: tmpShape(o.t, c), x: o.x + dx, y: o.y + dy, w: o.w, h: o.h, ok, label: `${o.x + dx}, ${o.y + dy}` } : null; }
    schedule(); return;
  }
  if (drag?.kind === 'msel') { const r = rectOf(drag, t); preview = r.w * r.h > 1 ? { kind: 'msel', x: r.x, y: r.y, w: r.w, h: r.h, ok: true, label: `${r.w} × ${r.h}` } : null; schedule(); return; }
  if (drag?.kind === 'gmove') {
    const dx = t.x - drag.sx, dy = t.y - drag.sy;
    if (dx || dy) drag.moved = true;
    if (drag.moved) { const { R, nx, ny } = mselPlace(drag.base, 0, dx, dy); preview = { kind: 'tpl', T: R, shapes: mselShapes(R, nx, ny), x: nx, y: ny, w: R.w, h: R.h, ok: !mselCheck(R, nx, ny), label: `${dx >= 0 ? '+' : ''}${dx}, ${dy >= 0 ? '+' : ''}${dy}` }; }
    schedule(); return;
  }
  if (drag?.kind === 'rect') { updateRectPreview(t); return; }
  if (tool === 'clone' && stampT) { lastT = t; const c = maskCells(t.x, t.y, stampT.w, stampT.h, stampT.mask); preview = c ? { kind: 'clone', shape: Object.assign(tmpShape(stampT.t, c, (stampT.d || []).map(([dx, dy]) => [t.x + dx, t.y + dy])), { f: fAbs(stampT.f, t.x, t.y) }), x: t.x, y: t.y, w: stampT.w, h: stampT.h, ok: fitsCells(stampT.t, c), label: sizeLabel(stampT.t, stampT.w, stampT.h) } : null; schedule(); }
  else if (tool === 'bld' && isFixed(curType) && !drag) { fxPreview(t); }
  else if (tool === 'stamp' && curTpl) {
    const T = curTpl.T, inside = t.x >= 0 && t.y >= 0 && t.x + T.w <= W && t.y + T.h <= H, st = inside ? tplFit(T, t.x, t.y) : T.b.map(() => 'out'), shapes = [];
    T.b.forEach((en, n) => { if (st[n] === 'same') return; const c = entryCells(t.x, t.y, en); if (c) { const o = tmpShape(en[0], c, (en[5] || []).map(([dx, dy]) => [t.x + dx, t.y + dy]), en[7] || null); o._clash = st[n] !== 'new'; shapes.push(o); } });
    const nN = st.filter(v => v === 'new').length, nS = st.filter(v => v === 'same').length, nC = st.filter(v => v === 'clash').length;
    preview = { kind: 'tpl', T, shapes, x: t.x, y: t.y, w: T.w, h: T.h, ok: inside, label: `${T.w} × ${T.h}${inside && (nS || nC) ? ` · ${nN} new${nS ? `, ${nS} already there` : ''}${nC ? `, ${nC} occupied` : ''}` : ''}` }; schedule(); }
  else if (preview && !drag) { preview = null; schedule(); }
});
cv.addEventListener('pointerup', e => {
  const t = tileAt(e);
  if (drag?.kind === 'pan') { cv.style.cursor = tool === 'pan' || tool === 'align' ? 'grab' : tool === 'sel' ? 'default' : 'crosshair'; if (drag.rc && Math.hypot(e.clientX - drag.sx, e.clientY - drag.sy) < 5 && tool !== 'sel') { drag = null; leaveTool(); return; } }
  else if (drag?.kind === 'layer') { idbPut(drag.L); }
  else if (drag?.kind === 'move' && drag.moved) {
    const o = drag.o, dx = t.x - drag.sx, dy = t.y - drag.sy, c = movedCells(o, dx, dy);
    if (c && fitsCells(o.t, c, [o]) && doorsFree(o.d.map(i => (((i / W) | 0) + dy) * W + (i % W) + dx), [o])) { commit(); o.f = fAbs(o.f, dx, dy); reshape(o, c, o.d.map(i => (((i / W) | 0) + dy) * W + (i % W) + dx)); selU = o.u; computeSelReach(); dirty(); }
    else toast('There is no room. Rooms may only touch at the wall, houses also directly, but not in front of an entrance.');
  } else if (drag?.kind === 'msel') { const r = rectOf(drag, t); if (r.w * r.h > 1) { mselFromRect(r, drag.add); if (msel) showRTab('sel'); } }
  else if (drag?.kind === 'gmove' && drag.moved) mselApply(0, t.x - drag.sx, t.y - drag.sy, drag.base);
  else if (drag?.kind === 'rect') applyRect(drag, t);
  drag = null; if (!['clone','stamp'].includes(tool)) preview = null; schedule();
});
cv.addEventListener('pointerleave', () => { if (!drag && (tool === 'clone' || tool === 'stamp' || (tool === 'bld' && isFixed(curType)))) { preview = null; schedule(); } });
cv.addEventListener('wheel', e => {
  e.preventDefault(); const r = cv.getBoundingClientRect(), mx = e.clientX - r.left, my = e.clientY - r.top;
  const nz = Math.max(0.5, Math.min(40, z * (e.deltaY < 0 ? 1.15 : 1 / 1.15)));
  ox = mx - (mx - ox) * nz / z; oy = my - (my - oy) * nz / z; z = nz; schedule();
}, { passive: false });
function sizeLabel(t, w, h) { return isWalled(t) ? `${w} × ${h} inner · ${w + 2} × ${h + 2} outer` : `${w} × ${h} · no wall`; }
function rectOf(d, t) { const x = Math.max(0, Math.min(d.sx, t.x)), y = Math.max(0, Math.min(d.sy, t.y)); const x2 = Math.min(W - 1, Math.max(d.sx, t.x)), y2 = Math.min(H - 1, Math.max(d.sy, t.y)); return { x, y, w: x2 - x + 1, h: y2 - y + 1 }; }
function buildPlan(r) {
  const cells = rectCells(r.x, r.y, r.w, r.h); if (!cells) return null;
  const targets = [...blds.values()].filter(o => o.t === curType && boxHit(o, r) && cells.some(k => o._set.has(k) || o._ring.has(k) || (!isWalled(o.t) && orthAdj(k, o._set))));
  const merged = targets.length ? [...new Set([...targets.flatMap(o => o.cells), ...cells])] : cells;
  return { cells, targets, merged, ok: fitsCells(curType, merged, targets) };
}
function updateRectPreview(t) {
  const r = rectOf(drag, t);
  if (tool === 'bld') {
    const p = buildPlan(r); if (!p) return;
    const sh = tmpShape(curType, p.merged);
    let label = p.targets.length ? `extended to ${sh.cells.length} tiles${isRect(sh) ? ` (${sh.w} × ${sh.h})` : ''}` : sizeLabel(curType, r.w, r.h);
    if (curType === '_home') { const fit = isRect(sh) && (houseFit(sh.w, sh.h, 'bottom') || houseFit(sh.w, sh.h, 'left')); label += fit ? ` · ${fit.n} ${fit.n === 1 ? 'house' : 'houses'} ${HOUSE_BASES[fit.bi].w}×${HOUSE_BASES[fit.bi].h}` : ' · no game size'; }
    preview = { kind: 'bld', shape: sh, ...r, ok: p.ok, label };
  } else preview = { kind: tool === 'erase' ? 'erase' : tool === 'cap' || tool === 'copy' || tool === 'exp' ? 'cap' : 'rect', ...r, ok: true, label: `${r.w} × ${r.h}` };
  schedule();
}
function applyRect(d, t) {
  const r = rectOf(d, t); if (r.w <= 0 || r.h <= 0) return;
  if (tool === 'bld') {
    const p = buildPlan(r);
    if (!p || !p.ok) { toast(isWalled(curType) ? 'No room: room plus wall ring overlaps another building or the map edge.' : 'There is already a building or a wall.'); return; }
    commit();
    if (p.targets.length) { const keep = p.targets[0], doors = p.targets.flatMap(o => o.d); keep.f = p.targets.flatMap(o => o.f || []); for (const o of p.targets.slice(1)) delB(o.u); reshape(keep, p.merged, doors); selU = keep.u; }
    else { const o = addB(curType, p.cells); selU = o.u; }
    computeSelReach(); dirty(); return;
  }
  if (tool === 'copy') { const T = captureTpl(r); if (!T.b.length && !T.ter.length && !T.cl.length) { toast('Nothing to copy inside the frame. Buildings must lie inside the frame including their wall.'); return; } const C = { id: 'copy', n: 'Copy', s: '', ...T }; curTpl = { T: C, base: C, rot: 0 }; setTool('stamp'); toast(`Copy ${T.w} × ${T.h} with ${T.b.length} buildings: click to place, R rotates, Esc ends.`); return; }
  if (tool === 'cap') { const T = captureTpl(r); if (!T.b.length && !T.ter.length && !T.cl.length) { toast('Nothing worth a template inside the frame. Buildings must lie inside the frame including their wall.'); return; } pendingCap = T; showCapForm(); return; }
  if (tool === 'erase') { eraseRect(r); return; }
  if (tool === 'exp') { openExport(r); return; }
  commit();
  if (tool === 'ceil') { let n = 0; for (let j = r.y; j < r.y + r.h; j++) for (let i = r.x; i < r.x + r.w; i++) { const k = j * W + i; if (ceilOk(k)) { ceil[k] = 1; n++; } } if (!n) toast('Ceilings only go on free ground and roads.'); dirty(); return; }
  const v = tool === 'road' ? 1 : 2; for (let j = r.y; j < r.y + r.h; j++) for (let i = r.x; i < r.x + r.w; i++) { const k = j * W + i; if (!occ[k] && !wcnt[k]) { terr[k] = v; if (v === 2) ceil[k] = 0; } }
  computeSelReach(); dirty();
}
function eraseRect(r) {
  const R = new Set(rectCells(r.x, r.y, r.w, r.h) || []);
  const changes = [];
  for (const o of blds.values()) {
    if (!boxHit(o, r)) continue;
    const rem = new Set();
    for (const k of R) {
      if (o._set.has(k)) { rem.add(k); continue; }
      if (!o._ring.has(k)) continue;
      if (wcnt[k] > 1 && selU && selU !== o.u && ownersOfRing(k).some(b => b.u === selU)) continue;
      const x = k % W, y = (k / W) | 0;
      for (const [dx, dy] of D4) { const nx = x + dx, ny = y + dy; if (inMap(nx, ny) && o._set.has(ny * W + nx)) rem.add(ny * W + nx); }
    }
    const dl = o.d.filter(i => R.has(i));
    if (rem.size || dl.length) changes.push({ o, rem, dl });
  }
  commit();
  for (const k of R) if (!occ[k] && !wcnt[k]) { terr[k] = 0; ceil[k] = 0; }
  let removed = 0, split = 0;
  for (const { o, rem, dl } of changes) {
    const left = o.cells.filter(c => !rem.has(c)), doors = o.d.filter(i => !dl.includes(i)), oldF = o.f;
    if (!left.length || (isFixed(o.t) && rem.size)) { delB(o.u); removed++; continue; }
    const comps = components(left);
    reshape(o, comps[0], doors);
    for (const c of comps.slice(1)) { const nb = addB(o.t, c, doors); nb.f = oldF; fKeep(nb); split++; }
  }
  computeSelReach(); dirty();
  if (split) toast(`A room fell apart. It became ${split + 1} separate rooms.`); else if (removed) toast(removed === 1 ? 'One building was completely inside the erase area and is gone.' : `${removed} buildings were completely inside the erase area.`);
}
function placeClone(t) {
  if (!stampT) return; const c = maskCells(t.x, t.y, stampT.w, stampT.h, stampT.mask);
  if (!fitsCells(stampT.t, c)) { toast('There is no room.'); return; }
  commit(); const o = addB(stampT.t, c, (stampT.d || []).map(([dx, dy]) => (t.y + dy) * W + t.x + dx)); if (stampT.f?.length) { o.f = fAbs(stampT.f, t.x, t.y); fKeep(o); } selU = o.u; computeSelReach(); dirty();
}
let lastT = null;
function fxPreview(t) {
  lastT = t; const v = fxCurItem(curType), p = fxOrigin(v, t), c = rectCells(p.x, p.y, v.w, v.h);
  preview = c ? { kind: 'clone', shape: tmpShape(curType, c, isWalled(curType) ? fxEntIdx(v, p.x, p.y).map(i => [i % W, (i / W) | 0]) : [], [v.g, v.s, v.r]), x: p.x, y: p.y, w: v.w, h: v.h, ok: fitsCells(curType, c) && (!isWalled(curType) || doorsFree(fxEntIdx(v, p.x, p.y))), label: fxName(curType, v) + (isWalled(curType) ? ` inner · ${v.w + 2} × ${v.h + 2} outer` : '') } : null;
  schedule();
}
function placeFx(t) {
  const v = fxCurItem(curType), p = fxOrigin(v, t), c = rectCells(p.x, p.y, v.w, v.h);
  if (!c || !fitsCells(curType, c)) { toast('There is no room.'); return; }
  if (isWalled(curType) && !doorsFree(fxEntIdx(v, p.x, p.y))) { toast('The entrance would lie in another building. Rotate (R) or move it.'); return; }
  commit(); const o = addB(curType, c, isWalled(curType) ? fxEntIdx(v, p.x, p.y) : [], [v.g, v.s, v.r]); selU = o.u; computeSelReach(); dirty();
}
// Gewählten Raum mit fester Größe auf eine andere Größe/Drehung setzen (linke obere Ecke bleibt)
function fxSet(o, n) {
  const c = rectCells(o.x, o.y, n.w, n.h);
  if (!c || !fitsCells(o.t, c, [o]) || (isWalled(o.t) && !doorsFree(fxEntIdx(n, o.x, o.y), [o]))) { toast(`${fxName(o.t, n)} does not fit here.`); refreshSel(); return false; }
  commit(); o.v = [n.g, n.s, n.r]; reshape(o, c, isWalled(o.t) ? fxEntIdx(n, o.x, o.y) : []); computeSelReach(); dirty(); return true;
}
function placeTpl(t) {
  if (!curTpl) return; const T = curTpl.T;
  if (t.x < 0 || t.y < 0 || t.x + T.w > W || t.y + T.h > H) { toast(`The template needs ${T.w} × ${T.h} tiles and sticks out over the map edge.`); return; }
  commit(); const c = tplPut(T, t.x, t.y, true); dirty();
  if (c.same || c.clash) toast(`${c.new} ${c.new === 1 ? 'building' : 'buildings'} placed.${c.same ? ` ${c.same} ${c.same === 1 ? 'was' : 'were'} already there.` : ''}${c.clash ? ` ${c.clash} skipped because something already stands there (red).` : ''}`);
}
function toggleDoor(t) {
  if (!inMap(t.x, t.y)) return; const i = t.y * W + t.x;
  const already = [...blds.values()].find(o => o.d.includes(i));
  let owner = already;
  if (!owner) { const c = [...blds.values()].filter(o => validDoor(o, i)); owner = c.find(o => o.u === selU) || c[0]; }
  if (!owner) { toast('Doors go into the wall ring, not into the corner. For buildings without a wall, right next to them.'); return; }
  commit();
  if (already) reshape(owner, owner.cells, owner.d.filter(k => k !== i)); else { if (terr[i] === 2) terr[i] = 0; reshape(owner, owner.cells, [...owner.d, i]); }
  selU = owner.u; computeSelReach(); dirty();
}
function computeSelReach() { selReach = null; const o = blds.get(selU); if (!o) return; const r = radiusOf(o.t); if (r == null) return; selReach = bfs(accessTiles(o), r); }
function rotate() {
  if (tool === 'clone' && stampT) { stampT = { ...stampT, w: stampT.h, h: stampT.w, mask: rotMask(stampT.mask, stampT.w, stampT.h), f: fRot(stampT.t, stampT.f, stampT.h), d: (stampT.d || []).map(([dx, dy]) => [stampT.h - 1 - dy, dx]) }; if (lastT) { const t = lastT; const c = maskCells(t.x, t.y, stampT.w, stampT.h, stampT.mask); preview = c ? { ...preview, shape: Object.assign(tmpShape(stampT.t, c, stampT.d.map(([dx, dy]) => [t.x + dx, t.y + dy])), { f: fAbs(stampT.f, t.x, t.y) }), w: stampT.w, h: stampT.h, ok: fitsCells(stampT.t, c) } : null; } updateHint(); schedule(); return; }
  if (tool === 'stamp' && curTpl) { curTpl = { ...curTpl, T: rotTpl(curTpl.T), rot: (curTpl.rot + 1) % 4 }; updateHint(); preview = null; schedule(); return; }
  if (tool === 'bld' && isFixed(curType)) { const c = fxCurItem(curType); if (!c.R) { toast('In the game this building has only one orientation.'); return; } fxTurn(curType); updateHint(); if (lastT) fxPreview(lastT); return; }
  if (msel) { mselApply(1, 0, 0); return; }
  const o = blds.get(selU); if (!o) return;
  if (isFixed(o.t)) { const v = fxOf(o); if (!v) { toast(`Choose a game size first: ${fxSizesTxt(o.t)}.`); return; } if (!v.R) { toast('In the game this building has only one orientation.'); return; } fxSet(o, fxFind(o.t, v.g, v.s, (v.r + 1) % (v.R + 1))); return; }
  const nc = []; for (const c of o.cells) { const x = c % W, y = (c / W) | 0, nx = o.x + (o.h - 1 - (y - o.y)), ny = o.y + (x - o.x); if (!inMap(nx, ny)) { toast('Rotated, it sticks out over the map edge.'); return; } nc.push(ny * W + nx); }
  if (!fitsCells(o.t, nc, [o])) { toast('Rotated, it does not fit here.'); return; }
  commit(); const nf = fAbs(fRot(o.t, fRel(o, o.x, o.y), o.h), o.x, o.y), before = o.f.length; o.f = nf; reshape(o, nc, o.d.map(i => { const x = i % W, y = (i / W) | 0; return (o.y + (x - o.x)) * W + o.x + (o.h - 1 - (y - o.y)); })); if (o.f.length < before) toast(`${before - o.f.length} furniture could not be rotated along.`); computeSelReach(); dirty();
}
function changeType(o, nt) {
  if (isFixed(nt) && !(isRect(o) && fxList(nt).some(v => v.w === o.w && v.h === o.h))) { toast(`${BT.get(nt)?.n || nt} exists in the game only in ${fxSizesTxt(nt)}. That does not fit ${o.w} × ${o.h}.`); refreshSel(); return; }
  if (!fitsCells(nt, o.cells, [o])) { toast('With the new type the wall ring does not fit here.'); refreshSel(); return; }
  commit(); const old = o.t; liftB(o); o.t = nt; o.f = []; o.p = null; mkB(o); if (isWalled(nt) !== isWalled(old)) o.d = []; o.d = o.d.filter(i => validDoor(o, i)); dropB(o); computeSelReach(); dirty();
}
window.addEventListener('keydown', e => {
  if ((e.ctrlKey || e.metaKey) && !e.altKey && e.key.toLowerCase() === 'k') { e.preventDefault(); openCmd(); return; }
  if (!cmdDlg.hidden) return;
  if (e.key === 'Escape' && !mapPop.hidden) { e.preventDefault(); toggleMapPop(false); return; }
  if (e.target.matches('input, textarea, select')) { if (e.key === 'Escape') e.target.blur(); return; }
  const k = e.key.toLowerCase();
  if ((e.ctrlKey || e.metaKey) && k === 'z') { e.preventDefault(); e.shiftKey ? redo() : undo(); return; }
  if ((e.ctrlKey || e.metaKey) && k === 'y') { e.preventDefault(); redo(); return; }
  if (ed && !furnDlg.hidden) { if (!(e.ctrlKey || e.metaKey || e.altKey) && edKey(e, k)) e.preventDefault(); return; }
  if (e.ctrlKey || e.metaKey || e.altKey) return;
  if (k === ' ') { spaceDown = true; cv.style.cursor = 'grab'; e.preventDefault(); return; }
  if ((k === 'e' || k === 'q') && tool === 'bld' && isFixed(curType)) { fxCycle(curType, k === 'e' ? 1 : -1); updateHint(); refreshSel(); if (lastT) fxPreview(lastT); return; }
  const map = { q:'sel', b:'build', d:'bld', s:'road', m:'wall', c:'ceil', v:'copy', w:'door', e:'erase', t:'stamp', k:'cap', a:'align', x:'exp' };
  if (map[k]) { setTool(map[k]); return; }
  if (k.startsWith('arrow') && tool === 'sel' && (msel || selU)) { e.preventDefault(); const s = e.shiftKey ? 10 : 1, d = { arrowleft: [-s, 0], arrowright: [s, 0], arrowup: [0, -s], arrowdown: [0, s] }[k]; if (d) groupStep(0, d[0], d[1]); return; }
  if (k === 'r') rotate();
  else if (k === 'h') setOv(ovMode === 'off' ? 'cov' : 'off');
  else if (k === 'f') fit();
  else if (k === '?') toggleHelp(true);
  else if (k === 'escape') { if (!expDlg.hidden) expDlg.hidden = true; else if (!helpEl.hidden) toggleHelp(false); else if (drag && drag.kind !== 'pan') { drag = null; preview = null; schedule(); } else if (tool !== 'sel') leaveTool(); else { msel = null; selU = 0; selReach = null; preview = null; refreshPanels(); schedule(); } }
  else if (k === 'delete' || k === 'backspace') { if (msel) mselDelete(); else if (selU) { commit(); delB(selU); selReach = null; dirty(); } }
});
window.addEventListener('keyup', e => { if (e.key === ' ') { spaceDown = false; cv.style.cursor = tool === 'pan' || tool === 'align' ? 'grab' : tool === 'sel' ? 'default' : 'crosshair'; } });

// ---------- template panel ----------
const [sNx, sNy, sK, sRim] = ['sNx','sNy','sK','sRim'].map(id => document.getElementById(id));
function sv() { const n = (el, lo, hi) => Math.max(lo, Math.min(hi, parseInt(el.value, 10) || lo)); return { nx: n(sNx, 1, 20), ny: n(sNy, 1, 20), k: n(sK, 1, 9), rim: sRim.checked }; }
function footUpd() { const g = gridTpl(sv()); document.getElementById('sFoot').textContent = `${g.w} × ${g.h}`; }
[sNx, sNy, sK, sRim].forEach(el => el.addEventListener(el === sRim ? 'change' : 'input', () => { sRim.disabled = sv().k === 1; footUpd(); if (tool === 'stamp' && curTpl?.base.id === 'grid') useGrid(); }));
function useGrid() { const T = gridTpl(sv()); curTpl = { T, base: T, rot: 0 }; setTool('stamp'); }
// PRESETS: entfällt seit Version 28 (Generator kennt nur noch den Baukasten 37)
document.getElementById('gridStamp').addEventListener('click', useGrid);
const LS_TPL = 'syx-bezirk-tpl';
function mineList() { try { return JSON.parse(lsGet(LS_TPL) || '[]'); } catch { return []; } }
function mineSave(l) { return lsSet(LS_TPL, JSON.stringify(l)); }
function tplBtn(T, onPick) {
  const b = document.createElement('button'); b.className = 'tpl' + (tool === 'stamp' && curTpl && curTpl.base.id === T.id ? ' on' : '');
  const sub = T.s || ((T.b.length ? `${T.b.length} buildings` : 'only roads and walls') + (T.cl?.length ? ', with ceilings' : ''));
  b.innerHTML = `<b>${esc(T.n)}</b><span class="sz">${T.w}×${T.h}</span><small>${esc(sub)}</small>`;
  b.prepend(tplThumb(T)); b.classList.add('th');
  b.addEventListener('click', onPick); return b;
}
let pendingCap = null, pendingDelTpl = null, pendingCatTpl = null;
// Kategorien: eingebaute nach TPL_CATS, eigene Vorlagen tragen den Kategorienamen in T.c (ohne Angabe: „Eigene“)
const LS_TCAT = 'syx-bezirk-tplcat';
let tcatOpen = (() => { try { const v = JSON.parse(lsGet(LS_TCAT) || 'null'); if (!v || typeof v !== 'object') return null; const o = {}; for (const [k, x] of Object.entries(v)) o[CAT_MIG[k] || k] = x; return o; } catch { return null; } })() || { 'Complete blocks': 1 };
const catOf = T => { const c = (T.c && String(T.c).trim()) || TPL_OWN; return CAT_MIG[c] || c; };
function catNames() { const n = TPL_CATS.map(c => c[1]); for (const T of mineList()) if (!n.includes(catOf(T))) n.push(catOf(T)); if (!n.includes(TPL_OWN)) n.push(TPL_OWN); return n; }
function catToggle(n, open) { tcatOpen = { ...tcatOpen, [n]: open ? 1 : 0 }; lsSet(LS_TCAT, JSON.stringify(tcatOpen)); }
function pickTpl(T) { curTpl = { T, base: T, rot: 0 }; setTool('stamp'); }
function setMineCat(id, c) {
  const l = mineList(), T = l.find(x => x.id === id); if (!T) return;
  c = c.trim().slice(0, 40) || TPL_OWN; T.c = c; if (!mineSave(l)) { toast('Saving is blocked in this browser.'); return; }
  catToggle(c, true); pendingCatTpl = null; refreshTpls(); toast(`“${T.n}” is now in “${c}”.`);
}
function catSelect(cur, onPick, label) {
  const sel = document.createElement('select'); sel.setAttribute('aria-label', label);
  for (const n of catNames()) { const o = document.createElement('option'); o.value = n; o.textContent = n; sel.appendChild(o); }
  const nw = document.createElement('option'); nw.value = '\u0000neu'; nw.textContent = 'New category …'; sel.appendChild(nw);
  sel.value = cur; sel.addEventListener('change', () => onPick(sel.value === '\u0000neu' ? null : sel.value)); return sel;
}
function mineRow(T) {
  const r = document.createElement('div'); r.className = 'mine';
  r.appendChild(tplBtn(T, () => pickTpl(T)));
  const ctl = document.createElement('div'); ctl.className = 'row';
  if (pendingCatTpl === T.id) {
    const inp = document.createElement('input'); inp.type = 'text'; inp.placeholder = 'Category name'; inp.setAttribute('aria-label', 'Name of the new category'); inp.maxLength = 40;
    const ok = document.createElement('button'); ok.className = 'btn primary sm'; ok.textContent = 'OK';
    const no = document.createElement('button'); no.className = 'btn sm'; no.textContent = 'Cancel';
    ok.addEventListener('click', () => { if (!inp.value.trim()) { inp.focus(); return; } setMineCat(T.id, inp.value); });
    inp.addEventListener('keydown', e => { if (e.key === 'Enter') ok.click(); else if (e.key === 'Escape') { e.stopPropagation(); no.click(); } });
    no.addEventListener('click', () => { pendingCatTpl = null; refreshTpls(); });
    ctl.append(inp, ok, no); setTimeout(() => inp.focus(), 0);
  } else {
    ctl.appendChild(catSelect(catOf(T), c => { if (c === null) { pendingCatTpl = T.id; refreshTpls(); } else if (c !== catOf(T)) setMineCat(T.id, c); }, `Category of “${T.n}”`));
    const d = document.createElement('button'); d.className = 'btn danger sm'; d.textContent = pendingDelTpl === T.id ? 'Really?' : 'Delete';
    d.addEventListener('click', () => { if (pendingDelTpl === T.id) { mineSave(mineList().filter(x => x.id !== T.id)); pendingDelTpl = null; if (curTpl?.base.id === T.id) curTpl = null; } else pendingDelTpl = T.id; refreshTpls(); });
    ctl.appendChild(d);
  }
  r.appendChild(ctl); return r;
}
const CHEV = '<svg viewBox="0 0 10 10" aria-hidden="true"><path d="M3 1.5L7 5 3 8.5"/></svg>';
const GEN_EL = document.getElementById('gridGen');
function refreshTpls() {
  const box = document.getElementById('tplCats'), gen = GEN_EL, mine = mineList();
  const q = document.getElementById('tSearch').value.trim().toLowerCase(), hit = T => !q || `${T.n} ${T.s || ''} ${catOf(T)}`.toLowerCase().includes(q);
  const groups = new Map(TPL_CATS.map(([k, n]) => [n, { bi: BUILTIN.filter(T => T.c === k && hit(T)), mine: [] }]));
  for (const T of mine) { if (!hit(T)) continue; const n = catOf(T); if (!groups.has(n)) groups.set(n, { bi: [], mine: [] }); groups.get(n).mine.push(T); }
  if (!groups.has(TPL_OWN)) groups.set(TPL_OWN, { bi: [], mine: [] });
  box.textContent = '';
  for (const [n, g] of groups) {
    const raster = n === TPL_CATS[0][1], cnt = g.bi.length + g.mine.length, open = q ? cnt > 0 : !!tcatOpen[n];
    if (!cnt && (n !== TPL_OWN || q)) continue;
    const wrap = document.createElement('div'); wrap.className = 'tcat';
    const hd = document.createElement('button'); hd.className = 'tcathead'; hd.setAttribute('aria-expanded', open ? 'true' : 'false');
    hd.innerHTML = `${CHEV}<span>${esc(n)}</span><b>${cnt}</b>`;
    const body = document.createElement('div'); body.className = 'tpls'; body.hidden = !open;
    hd.addEventListener('click', () => { const o = body.hidden; body.hidden = !o; hd.setAttribute('aria-expanded', o ? 'true' : 'false'); catToggle(n, o); });
    for (const T of g.bi) body.appendChild(tplBtn(T, () => pickTpl(T)));
    for (const T of g.mine) body.appendChild(mineRow(T));
    if (raster && !q) body.appendChild(gen);
    if (n === TPL_OWN && !g.mine.length) { const p = document.createElement('p'); p.className = 'muted'; p.textContent = 'Drag an area of the map with “Capture” (K) and save it as your own template.'; body.appendChild(p); }
    wrap.append(hd, body); box.appendChild(wrap);
  }
}
// Vergleich unabhängig von der Zerlegung in Läufe: ist eine Vorlage eine Drehung einer anderen?
function tplSig(T) {
  const cells = (L, hasV) => { const out = []; for (const e of L || []) { const [v, x, y, w, h] = hasV ? e : [1, ...e]; for (let j = y; j < y + h; j++) for (let i = x; i < x + w; i++) out.push(`${v}.${i}.${j}`); } return out.sort().join(' '); };
  const b = T.b.map(([t, x, y, w, h, d, m, v, f]) => JSON.stringify([t, x, y, w, h, (d || []).map(p => p.join(',')).sort(), m || null, v || null, (f || []).map(p => p.join(',')).sort()])).sort();
  return JSON.stringify([T.w, T.h, b, cells(T.ter, true), cells(T.cl, false)]);
}
function tplMatch(T) {
  const sigs = []; let R = { ...T, cl: T.cl || [] };
  for (let k = 0; k < 4; k++) { sigs.push(tplSig(R)); R = rotTpl(R); }
  for (const X of [...BUILTIN, ...mineList()]) { const sx = tplSig({ ...X, cl: X.cl || [] }), k = sigs.indexOf(sx); if (k >= 0) return { X, r: (4 - k) % 4 }; }
  return null;
}
function showCapForm() {
  showLTab('t'); const f = document.getElementById('capForm'); f.hidden = false; f.scrollIntoView({ block: 'nearest' });
  const m = tplMatch(pendingCap), lastCat = (() => { try { const c = lsGet(LS_TCAT + '-last') || TPL_OWN; return CAT_MIG[c] || c; } catch { return TPL_OWN; } })();
  const note = m ? `<p class="capnote">${m.r ? `This is “${esc(m.X.n)}”, ${m.r}× rotated with R.` : `Same as “${esc(m.X.n)}”.`} Saving works anyway.</p>` : '';
  f.innerHTML = `<div class="tpl on" style="cursor:default"><b>New template</b><span class="sz">${pendingCap.w}×${pendingCap.h}</span><small>${pendingCap.b.length} buildings${pendingCap.ter.length || pendingCap.cl.length ? ', with roads, walls or ceilings' : ''}</small></div>${note}
    <div class="row" style="margin-top:6px"><input type="text" id="capName" placeholder="Template name" aria-label="Template name" style="flex:1;min-width:0"></div>
    <div class="row" style="margin-top:4px"><input type="text" id="capCat" list="capCats" maxlength="40" placeholder="Category" aria-label="Category" value="${esc(lastCat)}" style="flex:1;min-width:0"><datalist id="capCats">${catNames().map(n => `<option value="${esc(n)}">`).join('')}</datalist></div>
    <div class="row" style="margin-top:4px"><button class="btn primary sm" id="capSave">Save</button><button class="btn sm" id="capDrop">Discard</button></div>`;
  const nm = document.getElementById('capName'), cat = document.getElementById('capCat'); nm.focus();
  document.getElementById('capSave').addEventListener('click', () => {
    const n = nm.value.trim(); if (!n) { toast('Please enter a name for the template.'); nm.focus(); return; }
    const c = cat.value.trim().slice(0, 40) || TPL_OWN;
    const T = { id: 'c' + Date.now(), n, s: '', c, ...pendingCap };
    const l = mineList().filter(x => x.n !== n); l.unshift(T);
    if (!mineSave(l)) { toast('Saving is blocked in this browser.'); return; }
    lsSet(LS_TCAT + '-last', c); catToggle(c, true);
    pendingCap = null; f.hidden = true; pickTpl(T); toast(`Template “${n}” saved in “${c}”.`);
  });
  for (const el of [nm, cat]) el.addEventListener('keydown', e => { if (e.key === 'Enter') document.getElementById('capSave').click(); });
  document.getElementById('capDrop').addEventListener('click', () => { pendingCap = null; f.hidden = true; refreshTpls(); });
}

// ---------- palette ----------
const palEl = document.getElementById('palette'), bSearch = document.getElementById('bSearch');
const collapsed = new Set(['husbandry','trade','military']);
function refreshPalette() {
  const q = bSearch.value.trim().toLowerCase(); palEl.textContent = '';
  for (const c of CAT_ORDER) {
    const list = B.filter(b => b.c === c && (!q || b.n.toLowerCase().includes(q))).sort((a, b) => a.n.localeCompare(b.n));
    if (!list.length) continue;
    const wrap = document.createElement('div'); wrap.className = 'cat';
    const hd = document.createElement('button'); hd.className = 'cathead'; hd.innerHTML = `<i style="background:${CAT_COL[c]}"></i>${CAT_DE[c]}<b>${list.length}</b>`;
    hd.setAttribute('aria-expanded', String(!(collapsed.has(c) && !q)));
    hd.addEventListener('click', () => { collapsed.has(c) ? collapsed.delete(c) : collapsed.add(c); refreshPalette(); });
    wrap.appendChild(hd);
    if (!collapsed.has(c) || q) for (const b of list) {
      const it = document.createElement('button'); it.className = 'bitem' + (b.id === curType ? ' on' : '');
      const r = radiusOf(b.id);
      it.innerHTML = `${b.i ? `<img src="${b.i}" alt="">` : ''}<span class="nm">${esc(b.n)}</span>${r ? `<span class="rad" title="Service-Radius">${r}</span>` : ''}${b.wl ? '<span class="wl" title="with wall ring"></span>' : ''}`;
      it.title = b.n + (b.wl ? ' · with wall ring' : ' · no wall') + (b.p ? ' · available in the Syx-Vis room planner' : '');
      it.addEventListener('click', () => pickBuilding(b.id));
      wrap.appendChild(it);
    }
    palEl.appendChild(wrap);
  }
  document.getElementById('bCount').textContent = `${B.length} types`;
  refreshRecent();
}
bSearch.addEventListener('input', refreshPalette);
// Recently used buildings (Syx Pack v35), kept in this browser
const LS_RECENT = 'syx-bezirk-recent';
let recentB = (() => { try { const v = JSON.parse(lsGet(LS_RECENT) || '[]'); return Array.isArray(v) ? v.filter(id => BT.has(id)) : []; } catch { return []; } })();
function pickBuilding(id) {
  curType = id; recentB = [id, ...recentB.filter(x => x !== id)].slice(0, 6); lsSet(LS_RECENT, JSON.stringify(recentB));
  setTool('bld'); refreshPalette(); refreshSel();
}
function refreshRecent() {
  const box = document.getElementById('recentBox'), el = document.getElementById('recent'); el.textContent = '';
  box.hidden = !recentB.length;
  for (const id of recentB) {
    const b = BT.get(id); if (!b) continue;
    const c = document.createElement('button'); c.className = 'chip' + (id === curType && BUILD.has(tool) ? ' on' : ''); c.title = b.n;
    c.innerHTML = `${b.i ? `<img src="${b.i}" alt="">` : ''}<span>${esc(b.n)}</span>`; c.addEventListener('click', () => pickBuilding(id)); el.appendChild(c);
  }
}

// ---------- panels ----------
const selBody = document.getElementById('selBody');
function b64u(bytes) { let s = ''; for (const c of bytes) s += String.fromCharCode(c); return btoa(s).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, ''); }
function fromB64u(str) { const s = atob(str.replace(/-/g, '+').replace(/_/g, '/')); const u = new Uint8Array(s.length); for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i); return u; }
function typeOptions(cur) { return CAT_ORDER.map(c => `<optgroup label="${CAT_DE[c]}">${B.filter(b => b.c === c).sort((a, b) => a.n.localeCompare(b.n)).map(b => `<option value="${b.id}"${b.id === cur ? ' selected' : ''}>${esc(b.n)}${b.wl ? ' ▢' : ''}</option>`).join('')}</optgroup>`).join(''); }
function mselPanel() {
  const bs = mselBlds(), byT = new Map(), tt = [...msel.tt].filter(ttHas);
  for (const o of bs) byT.set(o.t, (byT.get(o.t) || 0) + 1);
  const rows = [...byT].sort((a, b) => b[1] - a[1] || (BT.get(a[0])?.n || a[0]).localeCompare(BT.get(b[0])?.n || b[0]));
  const nR = tt.filter(k => terr[k] === 1 && !wcnt[k] && !occ[k]).length, nM = tt.filter(k => terr[k] === 2 && !wcnt[k] && !occ[k]).length, nC = tt.filter(k => ceil[k]).length;
  const { B } = mselTpl();
  selBody.innerHTML = `<div class="selhead"><div><div class="c">Multiple selection</div><div class="t">${bs.length} buildings${tt.length ? ' and area' : ''}</div></div></div>
    <dl class="kv"><dt>Frame</dt><dd>${B.w} × ${B.h}</dd>${rows.slice(0, 8).map(([t, n]) => `<dt>${esc(BT.get(t)?.n || t)}</dt><dd>${n}</dd>`).join('')}${rows.length > 8 ? `<dt>other types</dt><dd>${rows.slice(8).reduce((a, r) => a + r[1], 0)}</dd>` : ''}${nR ? `<dt>Road tiles</dt><dd>${nR}</dd>` : ''}${nM ? `<dt>Free wall tiles</dt><dd>${nM}</dd>` : ''}${nC ? `<dt>Ceiling tiles</dt><dd>${nC}</dd>` : ''}</dl>
    <div class="row"><button class="btn sm" id="msRot">Rotate (R)</button><button class="btn sm" id="msCap">Capture as template</button><button class="btn danger sm" id="msDel">Delete (Del)</button><button class="btn sm" id="msOff">Clear (Esc)</button></div>
    <p class="muted">Dragging moves everything in the selection, including roads, walls and ceilings. Arrow keys move by 1 tile, with Shift by 10. R rotates around the centre. Shift+click adds or removes a building, Shift+rectangle adds an area.</p>`;
  document.getElementById('msRot').addEventListener('click', () => mselApply(1, 0, 0));
  document.getElementById('msDel').addEventListener('click', mselDelete);
  document.getElementById('msOff').addEventListener('click', () => { msel = null; refreshPanels(); schedule(); });
  document.getElementById('msCap').addEventListener('click', () => { pendingCap = mselTpl().T; showCapForm(); });
}
function refreshSel() {
  if (tool === 'sel') updateHint();
  if (msel) { mselPanel(); return; }
  const o = blds.get(selU);
  if (!o) {
    selBody.innerHTML = `<p class="muted">Nothing selected. Click a building with <b>Select</b> (Q).</p>
      <dl class="keys"><dt>Q</dt><dd>Select and move</dd><dt>B</dt><dd>Build: rooms, roads, walls, doors …</dd><dt>T</dt><dd>Stamp a template</dd><dt>Ctrl+Z</dt><dd>Undo</dd><dt>Ctrl+K</dt><dd>Search buildings, templates, commands</dd></dl>
      <p class="muted"><button class="btn sm" id="selHelp">All shortcuts (?)</button></p>`;
    document.getElementById('selHelp').addEventListener('click', () => toggleHelp(true));
    return;
  }
  const b = BT.get(o.t), r = radiusOf(o.t), q = outerOf(o), rect = isRect(o);
  let reachTxt = '';
  if (r != null && selReach) { let n = 0; for (const v of selReach) if (v !== 65535) n++; let hh = 0, hc = 0; for (const x of blds.values()) if (HOME.has(x.t)) { hh++; if (accessTiles(x).some(i => selReach[i] !== 65535)) hc++; } reachTxt = `<dt>Tiles reached</dt><dd>${n.toLocaleString('en-US')}</dd><dt>Houses reached</dt><dd>${hc} of ${hh}</dd>`; }
  const resTxt = o.t === '_home' ? `<dt>Residents (estimated)</dt><dd>${fmt(residentsOf(o))}</dd>` : '';
  selBody.innerHTML = `
    <div class="selhead">${b?.i ? `<img src="${b.i}" alt="">` : ''}<div><div class="c" style="color:${CAT_COL[b?.c]}">${CAT_DE[b?.c] || ''}</div><div class="t">${esc(b?.n || o.t)}</div></div></div>
    <dl class="kv">
      <dt>Inner size</dt><dd>${rect ? `${o.w} × ${o.h} = ${o.cells.length}` : `${o.cells.length} tiles, outline ${o.w} × ${o.h}`}</dd>
      <dt>Outer size</dt><dd>${q.w} × ${q.h}${isWalled(o.t) ? '' : ' (no wall)'}</dd>
      <dt>Inner position</dt><dd>${o.x}, ${o.y}</dd>
      <dt>Doors</dt><dd>${o.d.length ? o.d.length : isWalled(o.t) ? '<span style="color:var(--warn)">none</span>' : 'whole edge'}</dd>
      ${resTxt}
      ${r != null ? `<dt>Radius${radiusAssumed(o.t) ? ' (assumed)' : ''}</dt><dd><input type="number" id="radIn" min="1" max="2000" value="${r}" aria-label="Radius for this building type"></dd>` : ''}
      ${reachTxt}
    </dl>
    ${b?.fx ? (() => { const v = fxOf(o); return `<label class="muted" for="fxSel">Game size</label><select id="fxSel">${v ? '' : '<option value="" selected>– choose –</option>'}${fxSizes(o.t).map((x, k) => (o.t !== HOME_T || x.s < FX_PICK_MAX || (v && v.g === x.g && v.s === x.s)) ? `<option value="${k}"${v && v.g === x.g && v.s === x.s ? ' selected' : ''}>${esc(fxName(o.t, x))}</option>` : '').join('')}</select><p class="muted" style="color:${v ? 'var(--good)' : 'var(--bad)'}">${v ? `Matches the game${v.R ? `, rotation ${v.r + 1} of ${v.R + 1}` : ''}. The export brings the furniture piece along.` : `${o.w} × ${o.h}${isRect(o) ? '' : ' (not a rectangle)'} does not exist in the game. Allowed: ${esc(fxSizesTxt(o.t))}.`}</p>${entBlocked(o) ? '<p class="muted" style="color:var(--bad)">An entrance lies in another building. Rotate or move it, otherwise the export is blocked.</p>' : ''}${o.t === HOME_T ? '<p class="muted">Houses may touch without a wall in between, also different types. The entrances must stay free.</p>' : ''}`; })() : ''}
    ${isWalled(o.t) && !o.d.length && o.t !== '_home' ? '<p class="muted">Without a door the planner assumes an access on every side. Use W to put a door into the wall ring.</p>' : ''}
    ${r != null ? `<p class="muted">The radius applies to all buildings of this type in the plan.${radOv[o.t] != null ? ' <button class="btn sm" id="radReset">Game value</button>' : ''}</p>` : ''}
    <label class="muted" for="typeSel">Change type</label>
    <select id="typeSel">${typeOptions(o.t)}</select>
    <div class="row">
      ${canFurnish(o.t) ? '<button class="btn primary" id="furnBtn">Furnish room</button>' : ''}
      <button class="btn" id="cloneBtn">Stamp</button>
      <button class="btn" id="rotBtn">Rotate</button>
      <button class="btn danger" id="delBtn">Delete</button>
    </div>
    ${(() => { const pr = prodOf(o); if (!pr) return ''; const fl = pr.b.pk === 'farm' || pr.b.pk === 'orchard', pa = pr.b.pk === 'pasture';
      return `<div class="prodbox"><div class="c">Production</div><dl class="kv">
        <dt>Workers</dt><dd>${(() => { const w = workersOf(o); return w ? esc(wkTxt(w)) : fmt(pr.wk, 1); })()} <span class="muted">(${esc(pr.src)})</span></dd>
        ${pr.eff !== 1 ? `<dt>Efficiency</dt><dd>${Math.round(pr.eff * 100)} %</dd>` : ''}
        ${fl ? `<dt>Yield factor</dt><dd>${fmt(pr.factor * 100, 0)} %</dd>` : ''}
        ${pr.X?.parts.length ? `<dt>Bonuses</dt><dd title="${esc(pr.X.parts.join(', '))}">× ${fmt(pr.X.x, 2)}</dd>` : ''}
        <dt>Output / day</dt><dd>${pr.out.map(([r, a]) => `${fmt(a, 1)} ${esc(resName(r))}`).join(' + ') || '–'}</dd>
        ${pr.inp.length ? `<dt>Consumption / day</dt><dd>${pr.inp.map(([r, a]) => `${fmt(a, 1)} ${esc(resName(r))}`).join(' + ')}</dd>` : ''}</dl>
        ${pr.b.rc.length > 1 ? `<label class="muted" for="rcSel">Recipe</label><select id="rcSel">${pr.b.rc.map((r, k) => `<option value="${k}"${k === pr.ri ? ' selected' : ''}>${esc(r.o.map(([x]) => resName(x)).join(' + '))}${r.i.length ? ' from ' + esc(r.i.map(([x]) => resName(x)).join(' + ')) : ''}</option>`).join('')}</select>${[...blds.values()].filter(x => x.t === o.t).length > 1 ? `<button class="btn sm" id="rcSelAll">Apply to all ${esc(pr.b.n)}</button>` : ''}` : ''}
        <div class="grid3">${fl || pa ? `<label for="soilIn">Soil %<input type="number" id="soilIn" min="0" max="200" step="1" value="${Math.round(pr.soil * 100)}"></label>` : ''}${fl ? `<label for="moistIn">Moisture %<input type="number" id="moistIn" min="0" max="100" step="1" value="${Math.round(pr.moist * 100)}"></label>` : ''}<label for="woIn">Workers by hand<input type="number" id="woIn" min="0" step="0.5" value="${o.p?.wo ?? ''}" placeholder="auto"></label></div>
        ${pr.note ? `<p class="muted">${esc(pr.note)}</p>` : ''}</div>`; })()}
    ${!isProd(o.t) ? (() => { const w = workersOf(o); return w ? `<p>Workers: ${esc(wkTxt(w))}${w.src ? ` <span class="muted">(${esc(w.src)})</span>` : ''}${w.note ? `<br><span class="muted">${esc(w.note)}</span>` : ''}</p>` : ''; })() : ''}
    ${canFurnish(o.t) ? (() => { const sm = fSummary(o); return `<p class="muted">${sm ? `Furniture: ${sm.n} pieces · ${sm.st.filter(x => !x.emp || !workersOf(o)).map(x => `${esc(x.name)} ${x.txt}`).join(' · ')}` : 'Not furnished yet.'}</p>`; })() : ''}
    ${(() => { const c = costOf(o); if (!c) return ''; const m = maintOf(o, c); return `<p class="muted">Construction costs: ${resList(c.res)}${c.mul > 1 ? ` (support surcharge × ${fmt(c.mul, 2)})` : ''}${c.nof ? ' · furniture still missing' : ''}${c.est ? ' · size factor estimated' : ''}${m ? `<br>Upkeep per day: ${fmt(m.jobs, 2)} jobs, ${fmt(m.mat, 2)} Material${m.iso < 1 - 1e-9 ? ` (isolation ${fmtPct(m.iso)})` : ''}` : ''}</p>`; })()}
    ${upSelHtml(o)}
    ${o.f?.length && !isFixed(o.t) ? '<div class="row"><button class="btn sm" id="copyF">Copy furnishing to identical rooms</button></div>' : ''}`;
  const ri = document.getElementById('radIn');
  if (ri) ri.addEventListener('change', () => { const v = parseInt(ri.value, 10); if (v > 0) { commit(); radOv[o.t] = v; computeSelReach(); dirty(); refreshPalette(); } });
  document.getElementById('radReset')?.addEventListener('click', () => { commit(); delete radOv[o.t]; computeSelReach(); dirty(); refreshPalette(); });
  document.getElementById('typeSel').addEventListener('change', e => changeType(o, e.target.value));
  document.getElementById('fxSel')?.addEventListener('change', e => { const n0 = fxSizes(o.t)[+e.target.value]; if (!n0) return; const cur = fxOf(o); fxSet(o, fxFind(o.t, n0.g, n0.s, Math.min(cur ? cur.r : 0, n0.R))); });
  document.getElementById('entBtn')?.addEventListener('click', () => { const hc = houseCheck(o); if (!hc?.ok) return; commit(); reshape(o, o.cells, hc.ent); computeSelReach(); dirty(); toast(`${hc.ent.length} ${hc.ent.length === 1 ? 'door' : 'doors'} placed at the entrances.`); });
  document.getElementById('cloneBtn').addEventListener('click', () => cloneFrom(o));
  document.getElementById('furnBtn')?.addEventListener('click', () => openFurnish(o));
  const setP = (k, v) => { commit(); o.p = { ...(o.p || {}) }; if (v == null) delete o.p[k]; else o.p[k] = v; dirty(); };
  document.getElementById('rcSel')?.addEventListener('change', e => setRecipe(o, +e.target.value, false));
  document.getElementById('rcSelAll')?.addEventListener('click', () => setRecipe(o, +document.getElementById('rcSel').value, true));
  document.getElementById('soilIn')?.addEventListener('change', e => { const v = parseFloat(e.target.value); setP('soil', v >= 0 ? v : null); });
  document.getElementById('moistIn')?.addEventListener('change', e => { const v = parseFloat(e.target.value); setP('moist', v >= 0 ? Math.min(100, v) : null); });
  document.getElementById('woIn')?.addEventListener('change', e => { const v = parseFloat(e.target.value); setP('wo', e.target.value !== '' && v >= 0 ? v : null); });
  document.getElementById('upSel')?.addEventListener('change', e => { const v = +e.target.value; setP('up', v > 0 ? v : null); });
  document.getElementById('copyF')?.addEventListener('click', () => copyFurnish(o));
  document.getElementById('rotBtn').addEventListener('click', rotate);
  document.getElementById('delBtn').addEventListener('click', () => { commit(); delB(o.u); selReach = null; dirty(); });
}
const groupsEl = document.getElementById('groups');
function refreshGroups() {
  groupsEl.textContent = '';
  const present = new Set([...blds.values()].map(o => o.t));
  for (const g of GROUPS) {
    const has = g.t.some(t => present.has(t)), id = 'g-' + g.k;
    const cb = document.createElement('input'); cb.type = 'checkbox'; cb.id = id; cb.checked = groupOn[g.k];
    cb.addEventListener('change', () => { groupOn[g.k] = cb.checked; needOv = true; schedule(); refreshCov(); refreshLoadBox(); });
    const lb = document.createElement('label'); lb.htmlFor = id; lb.textContent = g.n + (has ? '' : ' · missing'); if (!has) lb.style.color = 'var(--fg-3)';
    const rr = document.createElement('button'); rr.className = 'r';
    const rs = [...new Set(g.t.map(radiusOf).filter(v => v != null))]; rr.textContent = rs.length > 2 ? `${Math.min(...rs)}–${Math.max(...rs)}` : rs.join('/');
    rr.title = 'Distance view for ' + g.n; if (ovMode === 'dist' && distGroup === g.k) rr.style.color = 'var(--gold-hi)';
    rr.addEventListener('click', () => { distGroup = g.k; setOv('dist'); });
    groupsEl.append(cb, lb, rr);
  }
}
function setOv(m) {
  ovMode = m; for (const b of document.querySelectorAll('#ovMode button, #ovMode2 button')) b.classList.toggle('on', b.dataset.m === m);
  if (m === 'load' && (!load || loadStale)) computeLoad();
  needOv = true; schedule(); refreshGroups(); refreshOvNote(); refreshLegend(); refreshLoadBox(); refreshAna();
}
document.querySelectorAll('#ovMode button, #ovMode2 button').forEach(b => b.addEventListener('click', () => setOv(b.dataset.m)));
function refreshOvNote() {
  const g = GROUPS.find(x => x.k === distGroup);
  document.getElementById('ovNote').textContent = ovMode === 'cov' ? 'Green: all chosen services reachable. Yellow: some. Red: none.'
    : ovMode === 'dist' ? `Walking distance to the nearest service “${g.n}”. Choose the group with the radius number on the right.`
    : OV2.includes(ovMode) ? OV2_NOTE[ovMode]
    : ovMode === 'load' ? 'Each house counts at the nearest reachable building per service. Houses: green served, yellow at an overloaded building, red without a building in range.'
    : 'Overlay is off.';
}
const loadBox = document.getElementById('loadBox');
function refreshLoadBox() {
  if (ovMode !== 'load') { loadBox.textContent = ''; return; }
  const act = GROUPS.filter(g => groupOn[g.k]);
  let h = `${loadStale ? '<p class="stale">Plan changed. Update with “Recalculate”.</p>' : ''}<div class="row"><button class="btn sm primary" id="loadRun">Recalculate</button></div>`;
  h += `<div class="lrow" style="color:var(--fg-3);font-size:11px"><span>Service</span><span>Res./bldg.</span><span>Status</span></div>`;
  for (const g of act) {
    const byB = load?.per[g.k]?.byB, vals = byB ? [...byB.values()] : [], cap = capOf(g);
    const tot = vals.reduce((s, v) => s + v, 0), mx = vals.length ? Math.max(...vals) : 0, over = cap ? vals.filter(v => v > cap).length : 0;
    const visits = tot * (NEEDS[g.need]?.r ?? 0) * needMult(g.need);
    const s = !vals.length ? 'no building' : `${vals.length} bldg. · max ${Math.round(mx)} E.${cap ? ` · ${over} overloaded` : ''} · ≈ ${fmt(visits)} visits/day`;
    h += `<div class="lrow"><label for="cap-${g.k}">${g.n}</label><input type="number" id="cap-${g.k}" min="1" step="1" placeholder="–" value="${calc.cap[g.k] ?? ''}" aria-label="Residents per building for ${g.n}"><span class="s">${s}</span></div>`;
  }
  h += '<p class="muted">Without an entry the colour only shows which building serves the most residents. You set “Res./bldg.” from your experience in the game.</p>';
  loadBox.innerHTML = h;
  document.getElementById('loadRun').addEventListener('click', runCalc);
  for (const g of act) document.getElementById('cap-' + g.k).addEventListener('change', e => { const v = parseFloat(e.target.value); if (v > 0) calc.cap[g.k] = v; else delete calc.cap[g.k]; needOv = true; schedule(); refreshLoadBox(); autosave(); });
}
function refreshLegend() {
  const cats = CAT_ORDER.filter(c => [...blds.values()].some(o => BT.get(o.t)?.c === c));
  let h = cats.map(c => `<span><i style="background:${CAT_COL[c]}"></i>${CAT_DE[c]}</span>`).join('');
  h += `<span><i style="background:rgb(${COL_RING})"></i>Wall ring</span><span><i style="background:rgb(${COL_DOOR})"></i>Door</span><span><i style="background:rgb(${COL_ROAD})"></i>Road</span><span><i style="background:rgb(${COL_WALL})"></i>Free wall</span>${ceil.some(v => v) ? `<span><i style="background:rgb(${COL_CEIL})"></i>Ceiling</span>` : ''}`;
  if (ovMode === 'cov') h += `<span><i style="background:${GOOD}"></i>full</span><span><i style="background:${WARN}"></i>partly</span><span><i style="background:${BAD}"></i>none</span>`;
  if (ovMode === 'shape') h += `<span><i style="background:${GOOD}"></i>round</span><span><i style="background:${BAD}"></i>square</span>`;
  if (['iso', 'commute', 'stock'].includes(ovMode)) h += `<span><i style="background:${GOOD}"></i>100 %</span><span><i style="background:${WARN}"></i>ab 75 %</span><span><i style="background:${BAD}"></i>below</span>`;
  if (ovMode === 'maint') h += `<span><i style="background:${GOOD}"></i>little</span><span><i style="background:${BAD}"></i>much upkeep per tile</span>`;
  if (ovMode === 'load') h += `<span><i style="background:${GOOD}"></i>served</span><span><i style="background:${WARN}"></i>overloaded</span><span><i style="background:${BAD}"></i>no service</span>`;
  h += '<span>1 grid = 10 tiles</span>';
  document.getElementById('legend').innerHTML = h;
}
document.querySelectorAll('#covWho button').forEach(b => b.addEventListener('click', () => { covWho = b.dataset.w; refreshCov(); }));
function refreshCov() {
  for (const b of document.querySelectorAll('#covWho button')) b.classList.toggle('on', b.dataset.w === covWho);
  if (reachDirty) computeReach();
  const target = [...blds.values()].filter(o => covWho === 'home' ? HOME.has(o.t) : WORKCAT.has(BT.get(o.t)?.c) && !HOME.has(o.t));
  const el = document.getElementById('covBars'); el.textContent = '';
  if (!target.length) { el.innerHTML = `<p class="muted">No ${covWho === 'home' ? 'houses' : 'workplaces'} in the plan yet.</p>`; return; }
  const area = target.reduce((s, o) => s + o.cells.length, 0);
  for (const g of GROUPS.filter(g => groupOn[g.k])) {
    const cov = target.filter(o => bldCovered(o, g)).reduce((s, o) => s + o.cells.length, 0), p = Math.round(cov / area * 100);
    const col = p >= 90 ? GOOD : p >= 50 ? WARN : BAD;
    const r = document.createElement('div'); r.className = 'bar';
    r.innerHTML = `<span>${g.n}</span><span class="track"><span class="fill" style="width:${p}%;background:${col}"></span></span><span class="pct">${p} %</span>`;
    el.appendChild(r);
  }
  const p = document.createElement('p'); p.className = 'muted';
  p.textContent = `${target.length} ${covWho === 'home' ? 'houses' : 'workplaces'}, weighted by inner area. Target from the guide: above 90 %.`;
  el.appendChild(p);
}
function refreshStats() {
  let road = 0, wall = 0, ring = 0, cei = 0; for (let i = 0; i < W * H; i++) { if (ceil[i]) cei++; if (wcnt[i]) ring++; else if (terr[i] === 1) road++; else if (terr[i] === 2) wall++; }
  const byCat = {}; let inner = 0;
  for (const o of blds.values()) { const c = BT.get(o.t)?.c; byCat[c] = (byCat[c] || 0) + 1; inner += o.cells.length; }
  const homes = [...blds.values()].filter(o => HOME.has(o.t));
  document.getElementById('planStats').innerHTML = `<dt>Map</dt><dd>${W} × ${H}</dd><dt>Buildings</dt><dd>${blds.size}</dd>` +
    CAT_ORDER.filter(c => byCat[c]).map(c => `<dt style="padding-left:10px">${CAT_DE[c]}</dt><dd>${byCat[c]}</dd>`).join('') +
    `<dt>Houses, inner area</dt><dd>${homes.reduce((s, o) => s + o.cells.length, 0).toLocaleString('en-US')}</dd>` +
    `<dt>Inner areas total</dt><dd>${inner.toLocaleString('en-US')}</dd><dt>Wall ring tiles</dt><dd>${ring.toLocaleString('en-US')}</dd><dt>Road</dt><dd>${road.toLocaleString('en-US')}</dd><dt>Free wall</dt><dd>${wall.toLocaleString('en-US')}</dd><dt>Ceilings</dt><dd>${cei.toLocaleString('en-US')}</dd>`;
}
let panelT = 0;
function refreshPanels() { clearTimeout(panelT); panelT = setTimeout(() => { if (lastStatT) status(lastStatT); refreshSel(); refreshGroups(); refreshCov(); refreshStats(); refreshLegend(); refreshLoadBox(); markCalcStale(); if (OV2.includes(ovMode)) refreshAna(); }, 30); }
const stEl = document.getElementById('status');
let lastStatT = null;
function status(t) {
  lastStatT = t; const so = blds.get(selU);
  let s = `<span>Tool <b>${esc(TOOL_NAME[tool] || tool)}</b></span>${msel ? `<span>Selection <b>${msel.us.size} buildings${msel.tt.size ? ' + area' : ''}</b></span>` : so ? `<span>Selection <b>${esc(BT.get(so.t)?.n || so.t)} ${so.w} × ${so.h}</b></span>` : ''}`;
  s += `<span>Zoom <b>${z.toFixed(1)} px</b></span>`;
  if (inMap(t.x, t.y)) {
    const i = t.y * W + t.x, o = blds.get(occ[i]);
    const what = o ? BT.get(o.t)?.n : wcnt[i] ? (dcnt[i] ? 'Door' : 'Wall ring' + (wcnt[i] > 1 ? ', shared' : '')) : terr[i] === 1 ? 'Road' : terr[i] === 2 ? 'Free wall' : 'Ground';
    s += `<span>Tile <b>${t.x}, ${t.y}</b></span><span><b>${esc(what)}${ceil[i] ? ' · ceiling' : ''}</b></span>`;
    if (ovMode === 'load' && load && o) {
      const hi = load.houses.indexOf(o);
      if (hi >= 0) s += `<span>Residents <b>${fmt(load.res[hi])}</b> · ${GROUPS.filter(g => groupOn[g.k]).map(g => g.n + (load.per[g.k].who[hi] ? '' : ' missing')).filter(x => x.endsWith('missing')).join(', ') || 'all services assigned'}</span>`;
      for (const g of GROUPS) { const v = load.per[g.k].byB.get(o.u); if (v != null) s += `<span>serves <b>${Math.round(v)} residents</b></span>`; }
    } else if (ovMode !== 'off' && ovMode !== 'load' && !reachDirty && walkable(i)) { const act = GROUPS.filter(g => groupOn[g.k]); const hit = act.filter(g => groupDistAt(g, i) !== 65535); s += `<span>Services <b>${hit.length}/${act.length}</b>${hit.length < act.length ? ' · missing: ' + act.filter(g => !hit.includes(g)).map(g => g.n).join(', ') : ''}</span>`; }
    if (selReach && selReach[i] !== 65535) s += `<span>Walking distance to selection <b>${selReach[i]}</b></span>`;
  }
  stEl.innerHTML = s;
}

// ---------- Bedarfsrechner ----------
const calcBody = document.getElementById('calcBody'), calcStamp = document.getElementById('calcStamp');
let calcStale = true, calcShown = false;
function markCalcStale() { if (!calcShown) return; calcStale = true; calcStamp.textContent = 'Plan changed'; calcStamp.style.color = 'var(--warn)'; }
const resName = id => id === '*' ? 'any' : (RES[id]?.n || id);
function computeCalc() {
  const houses = [...blds.values()].filter(o => o.t === '_home');
  const sizes = new Map();
  for (const o of houses) { const k = houseKey(o); if (!sizes.has(k)) sizes.set(k, { n: 0, def: houseDefault(o) }); sizes.get(k).n++; }
  const pop = houses.reduce((s, o) => s + residentsOf(o), 0);
  const sh = raceShares() || [{ r: null, f: 1 }];
  const food = new Map(), drink = new Map(); let foodT = 0, drinkT = 0;
  for (const { r, f } of sh) {
    const p = pop * f, fh = p * NEEDS.hunger.r * (r?.m.hunger ?? 1), fd = p * NEEDS.thirst.r * (r?.m.thirst ?? 1);
    foodT += fh; drinkT += fd;
    const fl = r ? r.food : ['*'], dl = r ? r.drink : ['*'];
    for (const x of fl) food.set(x, (food.get(x) || 0) + fh / fl.length);
    for (const x of dl) drink.set(x, (drink.get(x) || 0) + fd / dl.length);
  }
  const cl = CIVIC.find(e => e.id === 'clothes'), jw = CIVIC.find(e => e.id === 'jewelry');
  const clothes = pop * (cl?.w ?? 0) * Math.max(1, cl?.def ?? 1), jewelry = calc.jewelry ? pop * (jw?.w ?? 0) * 1 : 0;
  return { houses: houses.length, sizes, pop, food, foodT, drink, drinkT, clothes, jewelry };
}
function computeProd() {
  const per = new Map(), byType = new Map(); let jobs = 0, jobsMax = 0, open = 0, est = 0;
  const add = (r, k, a) => { const e = per.get(r) || { p: 0, c: 0 }; e[k] += a; per.set(r, e); };
  for (const o of blds.values()) {
    const w = workersOf(o); if (w && w.need != null) { jobs += w.need; jobsMax += w.max ?? w.need; if (w.est) est++; }
    const pr = prodOf(o); if (!pr) continue;
    if (pr.src === 'not furnished' || pr.src === 'please enter') open++;
    for (const [r, a] of pr.out) add(r, 'p', a); for (const [r, a] of pr.inp) add(r, 'c', a);
    const t = byType.get(o.t) || { n: 0, wk: 0, out: new Map() }; t.n++; t.wk += pr.wk; for (const [r, a] of pr.out) t.out.set(r, (t.out.get(r) || 0) + a); byType.set(o.t, t);
  }
  return { per, byType, jobs, jobsMax, open, est };
}
function prodHtml(c, days) {
  const P = computeProd(), dd = v => fmt(v * days), sg = v => `<span style="color:var(--${v >= -1e-6 ? 'good' : 'bad'})">${v > 0 ? '+' : ''}${fmt(v * days)}</span>`;
  if (!P.byType.size) return `<h3 class="ch">Production</h3>${P.jobs ? `<p><b>${fmt(P.jobs, 0)}</b> workers needed <span class="muted">· at most ${fmt(P.jobsMax, 0)} (all rooms)</span></p>` : ''}<p class="muted">No workplaces in the plan yet. Workshops and refineries count once they are furnished; fields are calculated from area, soil and moisture.</p>`;
  const cat = r => RES[r]?.c;
  const need = new Map(); // Ressource -> Bedarf pro Tag (nur mit Rassen genau, sonst Summe je Kategorie)
  if (calc.racesOn) { for (const [r, v] of c.food) need.set(r, v); for (const [r, v] of c.drink) need.set(r, v); }
  need.set('clothes', (need.get('clothes') || 0) + c.clothes); if (c.jewelry) need.set('jewelry', (need.get('jewelry') || 0) + c.jewelry);
  const rows = [...new Set([...P.per.keys(), ...need.keys()])].filter(r => r !== '*').sort((a, b) => (cat(a) || 'z').localeCompare(cat(b) || 'z') || resName(a).localeCompare(resName(b)));
  let h = `<h3 class="ch">Production and balance</h3><div class="row" style="gap:12px"><span><b>${fmt(P.jobs, 0)}</b> workers needed</span><span class="muted">at most ${fmt(P.jobsMax, 0)}</span><span><b>${fmt(c.pop, 0)}</b> residents</span>${c.pop ? `<span class="muted">${fmt(P.jobs / c.pop * 100, 0)} % of residents</span>` : ''}</div>`;
  if (P.open) h += `<p class="stale">${P.open} ${P.open === 1 ? 'workplace is' : 'workplaces are'} not furnished yet or without a worker count and count as 0.</p>`;
  h += `<table class="ctab"><tr><th>Good</th><th class="n">produced</th><th class="n">consumed</th><th class="n">demand</th><th class="n">balance</th></tr>`;
  for (const r of rows) { const e = P.per.get(r) || { p: 0, c: 0 }, n = need.get(r) || 0; h += `<tr><td>${esc(resName(r))}</td><td class="n">${e.p ? dd(e.p) : ''}</td><td class="n">${e.c ? dd(e.c) : ''}</td><td class="n">${n ? dd(n) : ''}</td><td class="n">${sg(e.p - e.c - n)}</td></tr>`; }
  if (!calc.racesOn) for (const [k, lbl, tot] of [['food', 'Food total', c.foodT], ['drink', 'Drinks total', c.drinkT]]) {
    let net = 0; for (const [r, e] of P.per) if (cat(r) === k) net += e.p - e.c;
    h += `<tr class="sum"><td>${lbl}</td><td class="n" colspan="2">${dd(net)} free</td><td class="n">${dd(tot)}</td><td class="n">${sg(net - tot)}</td></tr>`;
  }
  h += `</table><table class="ctab"><tr><th>Workplace</th><th class="n">No.</th><th class="n">Workers</th><th>Output</th></tr>`;
  for (const [t, v] of [...P.byType].sort((a, b) => b[1].wk - a[1].wk)) h += `<tr><td>${esc(BT.get(t)?.n || t)}</td><td class="n">${v.n}</td><td class="n">${fmt(v.wk, 0)}</td><td>${[...v.out].map(([r, a]) => `${dd(a)} ${esc(resName(r))}`).join(', ')}</td></tr>`;
  h += `</table><p class="muted">Output = recipe rate × workers × efficiency, fields additionally × soil × (0.05 + moisture × bonus) as in the game code. Consumed = inputs of the workshops. Demand without races only as a total for food and drinks. Not included: tech bonuses, seasons, drought, spoilage, worker skill.</p>`;
  return h;
}
function runCalc() { computeLoad(); renderCalc(); needOv = true; schedule(); refreshLoadBox(); }
function renderCalc() {
  const c = computeCalc(), days = calc.days > 0 ? calc.days : 1, dd = v => fmt(v * days);
  calcShown = true; calcStale = false; calcStamp.textContent = `As of ${new Date().toLocaleTimeString('en-US', { hour: '2-digit', minute: '2-digit' })}`; calcStamp.style.color = '';
  let h = `<div class="row" style="align-items:baseline;gap:10px"><span class="big">${fmt(c.pop, 0)}</span><span class="muted">residents in ${c.houses} houses</span></div>`;
  h += `<table class="ctab"><tr><th>House size inside</th><th class="n">Count</th><th class="n">Res./house</th></tr>`;
  for (const [k, v] of [...c.sizes].sort((a, b) => b[1].n - a[1].n)) h += `<tr><td>${esc(houseLabel(k))}</td><td class="n">${v.n}</td><td class="n"><input type="number" min="0" step="1" data-hk="${esc(k)}" placeholder="${v.def}" value="${calc.resOv[k] ?? ''}" aria-label="Residents per house ${esc(houseLabel(k))}"></td></tr>`;
  h += `</table><div class="row"><label class="muted" for="upf">Upgrade factor</label><input type="number" id="upf" min="0.1" max="5" step="0.1" value="${calc.upf}"><span class="muted">Forum value after both upgrades: about 1.8</span></div>`;
  h += `<div class="chkline"><input type="checkbox" id="racesOn"${calc.racesOn ? ' checked' : ''}><label for="racesOn">Split by races</label></div>`;
  if (calc.racesOn) {
    const on = RACES.filter(r => calc.races[r.id]?.on), sum = on.reduce((s, r) => s + (calc.races[r.id].share || 0), 0);
    h += '<div class="racegrid">' + RACES.map(r => `<input type="checkbox" id="rc-${r.id}"${calc.races[r.id]?.on ? ' checked' : ''}><label for="rc-${r.id}">${esc(r.n)}</label><input type="number" id="rs-${r.id}" min="0" max="100" step="1" value="${calc.races[r.id]?.on ? Math.round(calc.races[r.id].share) : ''}" aria-label="Share of ${esc(r.n)} in percent"${calc.races[r.id]?.on ? '' : ' disabled'}>`).join('') + '</div>';
    if (on.length && Math.round(sum) !== 100) h += `<p class="stale">Sum ${Math.round(sum)} %. Shares are applied proportionally.</p>`;
  }
  h += `<div class="row"><label class="muted" for="days">Period</label><input type="number" id="days" min="1" step="1" value="${days}"><span class="muted">days</span></div>`;
  h += `<table class="ctab"><tr><th>Good</th><th class="n">${days === 1 ? 'per day' : `pro ${days} days`}</th></tr>`;
  h += `<tr class="sum"><td>Food</td><td class="n">${dd(c.foodT)}</td></tr>`;
  if (calc.racesOn) for (const [k, v] of [...c.food].sort((a, b) => b[1] - a[1])) h += `<tr class="sub"><td>${esc(resName(k))}</td><td class="n">${dd(v)}</td></tr>`;
  h += `<tr class="sum"><td>Drinks</td><td class="n">${dd(c.drinkT)}</td></tr>`;
  if (calc.racesOn) for (const [k, v] of [...c.drink].sort((a, b) => b[1] - a[1])) h += `<tr class="sub"><td>${esc(resName(k))}</td><td class="n">${dd(v)}</td></tr>`;
  h += `<tr class="sum"><td>Clothing</td><td class="n">${dd(c.clothes)}</td></tr>`;
  if (calc.jewelry) h += `<tr class="sum"><td>Jewelry</td><td class="n">${dd(c.jewelry)}</td></tr>`;
  h += `</table><div class="chkline"><input type="checkbox" id="jewOn"${calc.jewelry ? ' checked' : ''}><label for="jewOn">Include jewelry (1 piece per resident)</label></div>`;
  h += prodHtml(c, days) + costHtml();
  h += `<p class="muted">Need rates from the game data (v71), read as consumption per head and day: food 0.5, drink 0.2, clothing 0.25 wear. Race factors included, favourite foods split evenly. Whether 1 rate is exactly 1 unit is not verified.</p>`;
  calcBody.innerHTML = h;
  costBind(() => { renderCalc(); autosave(); });
  const rer = () => { renderCalc(); autosave(); if (ovMode === 'load') { computeLoad(); needOv = true; schedule(); refreshLoadBox(); } };
  calcBody.querySelectorAll('input[data-hk]').forEach(inp => inp.addEventListener('change', () => { const v = parseFloat(inp.value); if (v >= 0 && inp.value !== '') calc.resOv[inp.dataset.hk] = v; else delete calc.resOv[inp.dataset.hk]; rer(); }));
  document.getElementById('upf').addEventListener('change', e => { const v = parseFloat(e.target.value); calc.upf = v > 0 ? v : 1; rer(); });
  document.getElementById('days').addEventListener('change', e => { const v = parseInt(e.target.value, 10); calc.days = v > 0 ? v : 1; renderCalc(); autosave(); });
  document.getElementById('jewOn').addEventListener('change', e => { calc.jewelry = e.target.checked; renderCalc(); autosave(); });
  document.getElementById('racesOn').addEventListener('change', e => {
    calc.racesOn = e.target.checked;
    if (calc.racesOn && !Object.keys(calc.races).length) { const share = 100 / RACES.length; for (const r of RACES) calc.races[r.id] = { on: true, share }; }
    rer();
  });
  if (calc.racesOn) for (const r of RACES) {
    document.getElementById('rc-' + r.id).addEventListener('change', e => {
      calc.races[r.id] = { ...(calc.races[r.id] || {}), on: e.target.checked };
      const on = RACES.filter(x => calc.races[x.id]?.on); for (const x of on) calc.races[x.id].share = 100 / on.length;
      rer();
    });
    document.getElementById('rs-' + r.id).addEventListener('change', e => { const v = parseFloat(e.target.value); calc.races[r.id] = { on: true, share: v >= 0 ? v : 0 }; rer(); });
  }
}
document.getElementById('calcBtn').addEventListener('click', runCalc);

// ---------- layers panel ----------
const layersEl = document.getElementById('layers'), alignBox = document.getElementById('alignBox');
let pendingDelLayer = null;
function refreshLayers() {
  layersEl.textContent = '';
  const sorted = [...layers].sort((a, b) => b.ord - a.ord);
  for (const L of sorted) {
    const active = L.id === actLayer && tool === 'align';
    const r = document.createElement('div'); r.className = 'layer' + (L.id === actLayer ? ' act' : '');
    r.innerHTML = `<img src="${L.url}" alt="">
      <select aria-label="Layer type">${Object.entries(KINDS).map(([k, n]) => `<option value="${k}"${k === L.kind ? ' selected' : ''}>${n}</option>`).join('')}</select>
      <input type="checkbox" aria-label="Layer visible" title="visible"${L.vis ? ' checked' : ''}>
      <button class="btn sm" title="one layer up">↑</button>
      <button class="btn sm danger" title="Delete layer">${pendingDelLayer === L.id ? '?' : '×'}</button>
      <div class="op">Opacity <input type="range" min="0.05" max="1" step="0.05" value="${L.op}" aria-label="Opacity"> <button class="btn sm${active ? ' on' : ''}" aria-pressed="${active}">${active ? 'Finish aligning' : 'Align'}</button></div>`;
    const btns = r.querySelectorAll('button'), sel = r.querySelector('select'), cb = r.querySelector('input[type=checkbox]'), rg = r.querySelector('input[type=range]');
    sel.addEventListener('change', () => { L.kind = sel.value; idbPut(L); });
    cb.addEventListener('change', () => { L.vis = cb.checked; idbPut(L); needBase = true; schedule(); });
    btns[0].addEventListener('click', () => { const above = sorted[sorted.indexOf(L) - 1]; if (above) { [L.ord, above.ord] = [above.ord, L.ord]; idbPut(L); idbPut(above); refreshLayers(); schedule(); } });
    btns[1].addEventListener('click', () => { if (pendingDelLayer === L.id) { layers = layers.filter(x => x !== L); idbDel(L.id); URL.revokeObjectURL(L.url); if (actLayer === L.id) actLayer = layers[0]?.id || null; pendingDelLayer = null; needBase = true; schedule(); if (tool === 'align' && !layers.length) setTool('sel'); } else pendingDelLayer = L.id; refreshLayers(); });
    rg.addEventListener('input', () => { L.op = parseFloat(rg.value); schedule(); });
    rg.addEventListener('change', () => idbPut(L));
    btns[2].addEventListener('click', () => { if (active) setTool('align'); else { actLayer = L.id; if (tool === 'align') refreshLayers(); else setTool('align'); } });
    layersEl.appendChild(r);
  }
  const L = layers.find(l => l.id === actLayer);
  if (!L) { alignBox.textContent = ''; return; }
  alignBox.innerHTML = `<div class="grid3">
      <label for="lX">X (tiles)<input type="number" id="lX" step="0.25" value="${L.x}"></label>
      <label for="lY">Y (tiles)<input type="number" id="lY" step="0.25" value="${L.y}"></label>
      <label for="lP">Pixels/tile<input type="number" id="lP" step="0.01" min="0.05" value="${+(L.ppt || 0).toFixed(3)}"></label>
    </div>
    <div class="row" style="margin-top:6px"><button class="btn sm" id="lFitW">Fit map width</button><button class="btn sm" id="lMap">Use map size</button>${L.ppt >= 1.5 ? '<button class="btn sm" id="lShrink">Shrink to 1 px per tile</button>' : ''}</div>
    <p class="muted" style="margin-top:6px">${KINDS[L.kind]}: ${L.img.naturalWidth} × ${L.img.naturalHeight} px, covers ${L.ppt ? (L.img.naturalWidth / L.ppt).toFixed(1) + ' × ' + (L.img.naturalHeight / L.ppt).toFixed(1) : '–'} tiles</p>`;
  const num = id => parseFloat(document.getElementById(id).value);
  for (const id of ['lX', 'lY', 'lP']) document.getElementById(id).addEventListener('change', () => { const p = num('lP'); L.x = num('lX') || 0; L.y = num('lY') || 0; if (p > 0) L.ppt = p; idbPut(L); refreshLayers(); schedule(); });
  document.getElementById('lFitW').addEventListener('click', () => { L.ppt = L.img.naturalWidth / W; L.x = 0; L.y = 0; idbPut(L); refreshLayers(); schedule(); toast('Layer stretched to the map width.'); });
  document.getElementById('lShrink')?.addEventListener('click', () => shrinkLayer(L));
  document.getElementById('lMap').addEventListener('click', () => {
    if (!L.ppt) return; const nw = Math.round(L.img.naturalWidth / L.ppt), nh = Math.round(L.img.naturalHeight / L.ppt);
    if (nw < 20 || nh < 20 || nw > 1024 || nh > 1024) { toast(`That would give ${nw} × ${nh} tiles. Allowed are 20 to 1024. Set “Pixels/tile” first.`); return; }
    document.getElementById('mapW').value = nw; document.getElementById('mapH').value = nh; document.getElementById('applySize').click();
  });
}
function shrinkLayer(L) {
  const k = L.ppt, tw = Math.round(L.img.naturalWidth / k), th = Math.round(L.img.naturalHeight / k);
  try {
    let src = L.img, w = L.img.naturalWidth, h = L.img.naturalHeight;
    while (w / 2 >= tw && h / 2 >= th) { const c = document.createElement('canvas'); c.width = Math.round(w / 2); c.height = Math.round(h / 2); const x = c.getContext('2d'); x.imageSmoothingEnabled = true; x.imageSmoothingQuality = 'high'; x.drawImage(src, 0, 0, c.width, c.height); src = c; w = c.width; h = c.height; }
    const out = document.createElement('canvas'); out.width = tw; out.height = th; const o2 = out.getContext('2d'); o2.imageSmoothingEnabled = true; o2.imageSmoothingQuality = 'high'; o2.drawImage(src, 0, 0, tw, th);
    out.toBlob(blob => {
      if (!blob) { toast('Shrinking did not work.'); return; }
      URL.revokeObjectURL(L.url); L.blob = blob; L.url = URL.createObjectURL(blob); L.x = Math.round(L.x); L.y = Math.round(L.y); L.ppt = 1;
      L.img = new Image(); L.img.onload = () => { needBase = true; refreshLayers(); schedule(); }; L.img.src = L.url;
      idbPut(L); toast(`Layer shrunk to ${tw} × ${th} pixels, 1 pixel = 1 tile.`);
    }, 'image/png');
  } catch { toast('The image is too large for this browser to shrink. Please shrink it beforehand with another tool.'); }
}
function syncAlign() { const x = document.getElementById('lX'), y = document.getElementById('lY'); const L = layers.find(l => l.id === actLayer); if (x && L) { x.value = L.x; y.value = L.y; } }
const fileIn = document.getElementById('layerFile'), dropEl = document.getElementById('drop');
fileIn.addEventListener('change', () => { addLayerFiles(fileIn.files); fileIn.value = ''; });
dropEl.addEventListener('dragover', e => { e.preventDefault(); dropEl.classList.add('over'); });
dropEl.addEventListener('dragleave', () => dropEl.classList.remove('over'));
dropEl.addEventListener('drop', e => { e.preventDefault(); dropEl.classList.remove('over'); addLayerFiles(e.dataTransfer.files); });
stage.addEventListener('dragover', e => { if ([...e.dataTransfer.types].includes('Files')) e.preventDefault(); });
stage.addEventListener('drop', e => { if (e.dataTransfer.files.length) { e.preventDefault(); addLayerFiles(e.dataTransfer.files); } });

// ---------- save / share ----------
const LS_PLANS = 'syx-bezirk-plans', LS_CUR = 'syx-bezirk-current2';
function lsGet(k) { try { return localStorage.getItem(k); } catch { return null; } }
function lsSet(k, v) { try { localStorage.setItem(k, v); return true; } catch { return false; } }
function rle(a) { const out = []; let v = a[0], n = 0; for (const x of a) { if (x === v) n++; else { out.push(v, n); v = x; n = 1; } } out.push(v, n); return out; }
function unrle(r, len) { const a = new Uint8Array(len); let p = 0; for (let k = 0; k + 1 < r.length && p < len; k += 2) { a.fill(r[k], p, Math.min(len, p + r[k + 1])); p += r[k + 1]; } return a; }
function toObj(withTpl) { const o = { v: 3, name: planName, W, H, t: rle(terr), ...(ceil.some(v => v) ? { c: rle(ceil) } : {}), b: [...blds.values()].map(o => [o.t, o.x, o.y, o.w, o.h, doorXY(o), maskOf(o), o.v || null, o.f?.length ? o.f : null, o.p || null]), r: radOv, calc }; if (withTpl) o.tp = mineList(); return o; }
function fromObj(p) {
  if (!p || ![1, 2, 3].includes(p.v) || !(p.W > 0) || !(p.H > 0)) throw new Error('Unknown format');
  W = Math.min(1024, p.W); H = Math.min(1024, p.H); allocGrids(); terr = unrle(p.t || [0, W * H], W * H); if (Array.isArray(p.c)) ceil = unrle(p.c, W * H);
  blds = new Map(); nextU = 1; radOv = p.r || {};
  if (p.calc) calc = { resOv: {}, upf: 1, racesOn: false, races: {}, jewelry: false, days: 1, cap: {}, ...p.calc };
  let lost = 0;
  for (const [t, x, y, w, h, d, m, v, f, pp] of p.b || []) { const c = BT.has(t) ? maskCells(x, y, w, h, m) : null; if (c && fitsCells(t, c)) { const o = addB(t, c, (d || []).map(([dx, dy]) => dy * W + dx), Array.isArray(v) ? v : null); if (Array.isArray(f) && f.length) { o.f = f; fKeep(o); } if (pp && typeof pp === 'object') o.p = pp; } else lost++; }
  if (Array.isArray(p.tp) && p.tp.length) { const mine = mineList(), names = new Set(mine.map(x => x.n)); const add = p.tp.filter(x => x && x.n && !names.has(x.n)); if (add.length) mineSave([...add, ...mine]); }
  planName = p.name || planName; selU = 0; selReach = null; load = null; syncSizeInputs();
  document.getElementById('planName').value = isSampleName(planName) ? '' : planName;
  return lost;
}
function syncSizeInputs() { document.getElementById('mapW').value = W; document.getElementById('mapH').value = H; document.getElementById('mapSizeTxt').textContent = `${W} × ${H}`; }
let saveT = 0;
function autosave() { clearTimeout(saveT); saveT = setTimeout(() => lsSet(LS_CUR, JSON.stringify(toObj(false))), 400); }
function plansList() { try { return JSON.parse(lsGet(LS_PLANS) || '[]'); } catch { return []; } }
let pendingDel = null;
function refreshPlans() {
  const el = document.getElementById('plans'); el.textContent = '';
  for (const [idx, p] of plansList().entries()) {
    const r = document.createElement('div'); r.className = 'plan';
    const nm = document.createElement('span'); nm.className = 'nm'; nm.textContent = `${p.name} · ${p.W}×${p.H}${p.v === 1 ? ' · old version' : ''}`;
    const ld = document.createElement('button'); ld.className = 'btn sm'; ld.textContent = 'Load';
    ld.addEventListener('click', () => { commit(); const lost = fromObj(p); dirty(); fit(); refreshTpls(); if (calcShown) renderCalc(); toast(lost ? `“${p.name}” loaded. ${lost} buildings no longer fitted with their wall ring.` : `“${p.name}” loaded.`); });
    const dl = document.createElement('button'); dl.className = 'btn sm danger'; dl.textContent = pendingDel === idx ? 'Really?' : 'Delete';
    dl.addEventListener('click', () => { if (pendingDel === idx) { const l = plansList(); l.splice(idx, 1); lsSet(LS_PLANS, JSON.stringify(l)); pendingDel = null; } else pendingDel = idx; refreshPlans(); });
    r.append(nm, ld, dl); el.appendChild(r);
  }
}
document.getElementById('saveBtn').addEventListener('click', () => {
  const n = document.getElementById('planName').value.trim(); if (!n) { toast('Please enter a name first.'); document.getElementById('planName').focus(); return; }
  planName = n; const l = plansList().filter(p => p.name !== n); l.unshift(toObj(false));
  if (lsSet(LS_PLANS, JSON.stringify(l.slice(0, 30)))) { toast(`“${n}” saved.`); refreshPlans(); } else toast('Saving is blocked in this browser. Use the plan code.');
});
async function pack(obj) {
  const raw = new TextEncoder().encode(JSON.stringify(obj));
  if (typeof CompressionStream === 'function') { const buf = await new Response(new Blob([raw]).stream().pipeThrough(new CompressionStream('deflate-raw'))).arrayBuffer(); return 'SYXB1z.' + b64u(new Uint8Array(buf)); }
  return 'SYXB1j.' + b64u(raw);
}
async function unpack(code) {
  const [h, body] = code.trim().split('.'); if (!body) throw new Error('no plan code');
  let bytes = fromB64u(body);
  if (h === 'SYXB1z') bytes = new Uint8Array(await new Response(new Blob([bytes]).stream().pipeThrough(new DecompressionStream('deflate-raw'))).arrayBuffer());
  else if (h !== 'SYXB1j') throw new Error('no plan code');
  return JSON.parse(new TextDecoder().decode(bytes));
}
const codeBox = document.getElementById('codeBox');
document.getElementById('copyCode').addEventListener('click', async () => {
  const c = await pack(toObj(true)); codeBox.value = c;
  try { await navigator.clipboard.writeText(c); toast(`Plan code copied (${c.length.toLocaleString('en-US')} characters).`); } catch { codeBox.focus(); codeBox.select(); toast('The code is in the field and selected. Copy it with Ctrl+C.'); }
});
document.getElementById('loadCode').addEventListener('click', async () => {
  try { const p = await unpack(codeBox.value); commit(); const lost = fromObj(p); dirty(); fit(); refreshTpls(); if (calcShown) renderCalc(); toast(lost ? `“${planName}” loaded. ${lost} buildings did not fit.` : `“${planName}” loaded.`); }
  catch { toast('The code could not be read. Please paste the complete code starting with “SYXB1”.'); }
});

// ---------- header ----------
document.getElementById('applySize').addEventListener('click', () => {
  const nw = Math.max(20, Math.min(1024, parseInt(document.getElementById('mapW').value, 10) || W));
  const nh = Math.max(20, Math.min(1024, parseInt(document.getElementById('mapH').value, 10) || H));
  commit(); const o = toObj(false);
  const nt = new Uint8Array(nw * nh), nc = new Uint8Array(nw * nh); for (let y = 0; y < Math.min(H, nh); y++) for (let x = 0; x < Math.min(W, nw); x++) { nt[y * nw + x] = terr[y * W + x]; nc[y * nw + x] = ceil[y * W + x]; }
  const lost = fromObj({ ...o, W: nw, H: nh, t: rle(nt), c: rle(nc) }); dirty(); fit(); toggleMapPop(false);
  toast(lost ? `The map is now ${nw} × ${nh}. ${lost} buildings were outside and were removed.` : `The map is now ${nw} × ${nh}.`);
});
let newArm = false;
document.getElementById('newMap').addEventListener('click', e => {
  const b = e.currentTarget;
  if (!newArm) { newArm = true; b.textContent = 'Really clear?'; b.classList.add('danger'); setTimeout(() => { newArm = false; b.textContent = 'New map'; b.classList.remove('danger'); }, 3000); return; }
  newArm = false; b.textContent = 'New map'; b.classList.remove('danger'); toggleMapPop(false);
  commit(); const nw = Math.max(20, Math.min(1024, parseInt(document.getElementById('mapW').value, 10) || 100)), nh = Math.max(20, Math.min(1024, parseInt(document.getElementById('mapH').value, 10) || 100));
  fromObj({ v: 3, name: 'New plan', W: nw, H: nh, t: [0, nw * nh], b: [], r: {}, calc }); dirty(); fit(); toast('Empty map created. Undo brings the old plan back.');
});
document.getElementById('undoBtn').addEventListener('click', undo);
document.getElementById('redoBtn').addEventListener('click', redo);
document.getElementById('fitBtn').addEventListener('click', fit);
const helpEl = document.getElementById('help');
function toggleHelp(v) { helpEl.hidden = !v; }
document.getElementById('helpBtn').addEventListener('click', () => toggleHelp(true));
document.getElementById('helpClose').addEventListener('click', () => toggleHelp(false));
helpEl.addEventListener('click', e => { if (e.target === helpEl) toggleHelp(false); });

// ---------- Syx Pack v35: tabs, map popover, header buttons, zoom, quick search ----------
const LS_UI = 'syx-bezirk-ui';
const uiTab = (() => { try { const v = JSON.parse(lsGet(LS_UI) || '{}'); return { l: ['b', 't'].includes(v.l) ? v.l : 'b', r: ['sel', 'views', 'eco', 'plan'].includes(v.r) ? v.r : 'sel' }; } catch { return { l: 'b', r: 'sel' }; } })();
function showTab(side, t) {
  const keys = side === 'l' ? ['b', 't'] : ['sel', 'views', 'eco', 'plan'], pre = side === 'l' ? 'lp-' : 'rp-';
  uiTab[side] = t; lsSet(LS_UI, JSON.stringify(uiTab));
  for (const b of document.querySelectorAll(`#${side}Tabs button`)) { const on = b.dataset.t === t; b.classList.toggle('on', on); b.setAttribute('aria-selected', String(on)); }
  for (const k of keys) document.getElementById(pre + k).hidden = k !== t;
}
const showLTab = t => showTab('l', t), showRTab = t => showTab('r', t);
document.querySelectorAll('#lTabs button').forEach(b => b.addEventListener('click', () => showLTab(b.dataset.t)));
document.querySelectorAll('#rTabs button').forEach(b => b.addEventListener('click', () => showRTab(b.dataset.t)));
showLTab(uiTab.l); showRTab(uiTab.r);
const mapPop = document.getElementById('mapPop'), mapBtn = document.getElementById('mapBtn');
function toggleMapPop(v) { mapPop.hidden = !v; mapBtn.setAttribute('aria-expanded', String(v)); if (v) { syncSizeInputs(); document.getElementById('mapW').select(); } }
mapBtn.addEventListener('click', () => toggleMapPop(mapPop.hidden));
document.addEventListener('pointerdown', e => { if (!mapPop.hidden && !e.target.closest('.hpop')) toggleMapPop(false); });
document.getElementById('mapFull').addEventListener('click', () => { document.getElementById('mapW').value = 768; document.getElementById('mapH').value = 768; });
for (const id of ['mapW', 'mapH']) document.getElementById(id).addEventListener('keydown', e => { if (e.key === 'Enter') document.getElementById('applySize').click(); });
document.getElementById('hdrImport').addEventListener('click', () => { showRTab('plan'); const sec = document.getElementById('importSec'); sec.scrollIntoView({ block: 'start' }); document.getElementById('bbBox').focus(); });
document.getElementById('hdrExport').addEventListener('click', () => setTool('exp'));
document.getElementById('tCap').addEventListener('click', () => setTool('cap'));
document.getElementById('tCopy').addEventListener('click', () => setTool('copy'));
document.getElementById('tSearch').addEventListener('input', () => refreshTpls());
const zValEl = document.getElementById('zVal');
function zoomBy(f) { const mx = vw / 2, my = vh / 2, nz = Math.max(0.5, Math.min(40, z * f)); ox = mx - (mx - ox) * nz / z; oy = my - (my - oy) * nz / z; z = nz; schedule(); }
document.getElementById('zIn').addEventListener('click', () => zoomBy(1.25));
document.getElementById('zOut').addEventListener('click', () => zoomBy(0.8));
document.getElementById('zFit').addEventListener('click', fit);
// Quick search (Ctrl+K): buildings, templates and commands in one list
const cmdDlg = document.getElementById('cmdDlg'), cmdIn = document.getElementById('cmdIn'), cmdList = document.getElementById('cmdList');
let cmdHits = [], cmdSel = 0;
function cmdAll() {
  const out = [], C = (n, sub, run, ki = '') => out.push({ n, sub, run, ki, cmd: true });
  for (const t of TOOLS) C(`${t.n}`, 'tool', () => setTool(t.k), t.key);
  for (const m of BMODES) C(`Build: ${m.n}`, 'tool', () => setTool(m.k), m.key);
  for (const b of document.querySelectorAll('#ovMode button, #ovMode2 button')) { const m = b.dataset.m; C(`Map view: ${b.textContent}`, 'view', () => { setOv(m); showRTab('views'); }); }
  C('Undo', 'edit', undo, 'Ctrl+Z'); C('Redo', 'edit', redo, 'Ctrl+Y'); C('Fit map', 'view', fit, 'F');
  C('Map size …', 'map', () => toggleMapPop(true));
  C('Recalculate demand and balance', 'economy', () => { showRTab('eco'); runCalc(); });
  C('Technologies …', 'economy', () => { showRTab('eco'); openTech(); });
  C('Production chain', 'analysis', () => { showRTab('eco'); openChain(); });
  C('Compare plans', 'plan', openCompare);
  C('Save plan …', 'plan', () => { showRTab('plan'); document.getElementById('planName').focus(); });
  C('Copy plan code', 'plan', () => { showRTab('plan'); document.getElementById('copyCode').click(); });
  C('Import from game …', 'plan', () => document.getElementById('hdrImport').click());
  C('Export to game', 'plan', () => setTool('exp'), 'X');
  C('Grid generator', 'templates', () => { showLTab('t'); document.getElementById('tSearch').value = ''; catToggle(TPL_CATS[0][1], true); refreshTpls(); GEN_EL.scrollIntoView({ block: 'nearest' }); document.getElementById('sNx').focus(); });
  C('Background layers', 'view', () => { showRTab('views'); document.getElementById('drop').scrollIntoView({ block: 'nearest' }); });
  C('Help and shortcuts', 'help', () => toggleHelp(true), '?');
  for (const b of B) out.push({ n: b.n, sub: CAT_DE[b.c] || 'building', img: b.i, run: () => pickBuilding(b.id) });
  for (const T of [...BUILTIN, ...mineList()]) out.push({ n: T.n, sub: `template · ${TPL_CATS.find(c => c[0] === T.c)?.[1] || catOf(T)} · ${T.w}×${T.h}`, run: () => { showLTab('t'); pickTpl(T); } });
  return out;
}
function cmdRender() {
  const q = cmdIn.value.trim().toLowerCase(), words = q.split(/\s+/).filter(Boolean), all = cmdAll();
  if (!words.length) cmdHits = [...recentB.map(id => all.find(x => !x.cmd && x.n === BT.get(id)?.n)).filter(Boolean), ...all.filter(x => x.cmd)].slice(0, 40);
  else {
    const sc = x => { const n = x.n.toLowerCase(), h = n + ' ' + x.sub.toLowerCase(); if (!words.every(w => h.includes(w))) return -1; return (n.startsWith(q) ? 3 : n.includes(q) ? 2 : 1) + (x.cmd ? 0.5 : 0); };
    cmdHits = all.map(x => [x, sc(x)]).filter(p => p[1] > 0).sort((a, b) => b[1] - a[1] || a[0].n.localeCompare(b[0].n)).slice(0, 60).map(p => p[0]);
  }
  cmdSel = Math.min(cmdSel, Math.max(0, cmdHits.length - 1));
  cmdList.innerHTML = cmdHits.length ? cmdHits.map((x, i) => `<li role="option" data-i="${i}" class="${i === cmdSel ? 'on' : ''}" aria-selected="${i === cmdSel}">${x.img ? `<img src="${x.img}" alt="">` : `<span class="ki">${x.cmd ? '›' : '▦'}</span>`}<span class="nm">${esc(x.n)}</span><small>${esc(x.sub)}</small>${x.ki ? `<span class="kbdh">${esc(x.ki)}</span>` : ''}</li>`).join('') : '<li class="muted">Nothing found.</li>';
  cmdList.querySelector('li.on')?.scrollIntoView({ block: 'nearest' });
}
function openCmd() { cmdDlg.hidden = false; cmdIn.value = ''; cmdSel = 0; cmdRender(); cmdIn.focus(); }
function closeCmd() { cmdDlg.hidden = true; }
function cmdRun(i) { const x = cmdHits[i]; if (!x) return; closeCmd(); x.run(); }
cmdIn.addEventListener('input', () => { cmdSel = 0; cmdRender(); });
cmdIn.addEventListener('keydown', e => {
  if (e.key === 'ArrowDown') { e.preventDefault(); cmdSel = Math.min(cmdHits.length - 1, cmdSel + 1); cmdRender(); }
  else if (e.key === 'ArrowUp') { e.preventDefault(); cmdSel = Math.max(0, cmdSel - 1); cmdRender(); }
  else if (e.key === 'Enter') { e.preventDefault(); cmdRun(cmdSel); }
  else if (e.key === 'Escape') { e.preventDefault(); closeCmd(); }
});
cmdList.addEventListener('click', e => { const li = e.target.closest('li[data-i]'); if (li) cmdRun(+li.dataset.i); });
cmdDlg.addEventListener('click', e => { if (e.target === cmdDlg) closeCmd(); });
document.getElementById('cmdBtn').addEventListener('click', openCmd);
let toastT = 0;
function toast(msg) { let t = document.querySelector('.toast'); if (!t) { t = document.createElement('div'); t.className = 'toast'; t.setAttribute('role', 'status'); document.body.appendChild(t); } t.textContent = msg; t.hidden = false; clearTimeout(toastT); toastT = setTimeout(() => { t.hidden = true; }, 3600); }

// ---------- Export für den Mod „Better Blueprints“ ----------
// Format aus dem Mod (BBPrintCodec, SavedPrints, v71): "SYX:BB" + [Meta]: + Base64(zlib(Text im Json-Format des Spiels))
const EXP_FLOORS = [['DIRT', 'Dirt road'], ['STONE_BRICK', 'Paved road'], ['SAND', 'Sand'], ['STONE_CROSS', 'STONE_CROSS'], ['STONE_LARGE_DARK', 'STONE_LARGE_DARK'], ['STONE_MEDIUM_DARK', 'STONE_MEDIUM_DARK'], ['WOOD', 'WOOD'], ['WOOD_SQUARE', 'WOOD_SQUARE']];
const WALL_JOB = 'JOB_WALL_WOOD';   // Material wählt das Spiel beim Platzieren
const CEIL_JOB = 'JOB_CEILING_WOOD'; // ebenso: Better Blueprints baut Decken als „Opening“ im gewählten Material, nur mit eingeschalteter Wand-Option
const NL = '\r\n';
class JE {
  constructor() { this.l = []; }
  raw(k, v) { this.l.push([k, String(v)]); return this; }
  str(k, v) { return this.raw(k, '"' + String(v).replace(/"/g, "'") + '"'); }
  ints(k, a) { return this.raw(k, '[' + NL + a.map(x => x + ',' + NL).join('') + ']'); }
  objs(k, a) { return this.raw(k, '[' + NL + a.map(o => '{' + NL + o.toString() + NL + '}' + ',' + NL).join('') + ']'); }
  obj(k, o) { return this.raw(k, '{' + NL + o.toString() + '}'); }
  toString(tabs = 0) { let b = ''; for (const [k, v] of this.l) { const ss = v.split(NL); b += '\t'.repeat(tabs) + k + ': ' + ss[0]; for (let i = 1; i < ss.length; i++) b += NL + '\t'.repeat(tabs) + (i < ss.length - 1 ? '\t' : '') + ss[i]; b += ',' + NL; } return b; }
}
let expFloor = (() => { try { return localStorage.getItem('syx-bezirk-floor') || 'DIRT'; } catch { return 'DIRT'; } })(), expData = null;
const expDlg = document.getElementById('expDlg'), expBody = document.getElementById('expBody');
function expCollect(r) {
  const inR = (x, y) => x >= r.x && y >= r.y && x < r.x + r.w && y < r.y + r.h;
  const rooms = [], problems = [], notes = []; let cut = 0, noDoor = 0, noExp = 0;
  for (const o of blds.values()) {
    const q = outerOf(o);
    const inside = q.x >= r.x && q.y >= r.y && q.x + q.w <= r.x + r.w && q.y + q.h <= r.y + r.h;
    if (!inside) { if (boxHit(o, r)) cut++; continue; }
    if (isFixed(o.t)) {
      if (BT.get(o.t).fx.noexp) { noExp++; continue; }
      const fx = fxOf(o); if (!fx) { problems.push({ o, msg: `${o.w} × ${o.h} does not exist in the game. Allowed: ${fxSizesTxt(o.t)}.` }); continue; }
      if (entBlocked(o)) { problems.push({ o, msg: 'An entrance lies in another building.' }); continue; }
      rooms.push({ o, fx });
    } else { if (isWalled(o.t) && !o.d.length) noDoor++; rooms.push({ o }); }
  }
  const roads = [], walls = [], ceils = [];
  for (let y = r.y; y < r.y + r.h; y++) for (let x = r.x; x < r.x + r.w; x++) { const i = y * W + x; if (occ[i] || wcnt[i]) continue; if (terr[i] === 1) roads.push([x - r.x, y - r.y]); else if (terr[i] === 2) walls.push([x - r.x, y - r.y]); if (ceil[i] && terr[i] !== 2) ceils.push([x - r.x, y - r.y]); }
  if (cut) notes.push(`${cut} ${cut === 1 ? 'building sticks' : 'buildings stick'} out over the frame and ${cut === 1 ? 'is missing' : 'are missing'} in the export.`);
  if (noExp) notes.push(`${noExp === 1 ? 'The throne is' : `${noExp} buildings are`} not included. You place it in the game yourself.`);
  if (noDoor) notes.push(`${noDoor} ${noDoor === 1 ? 'room has' : 'rooms have'} no door. They are included anyway, you then set the doors in the game.`);
  if (ceils.length) notes.push(`${ceils.length} ${ceils.length === 1 ? 'ceiling comes' : 'ceilings come'} along as a build order. Better Blueprints builds it only with the wall option switched on, in the material chosen there.`);
  return { r, rooms, problems, notes, roads, walls, ceils };
}
function roomPrint(o, hc, fx) {
  const w = o.w + 2, h = o.h + 2, d = new Array(w * h).fill(0);
  const at = i => ((((i / W) | 0) - o.y + 1) * w) + (i % W) - o.x + 1;
  for (const c of o.cells) d[at(c)] = 1;
  if (isWalled(o.t)) { for (const k of o._ring) d[at(k)] = 2; for (const k of (hc ? hc.ent : fx && fx.ent.length ? fxEntIdx(fx, o.x, o.y) : o.d)) d[at(k)] = 4; }
  if (!hc && !fx && o.f?.length) { const fu = furnOf(o.t); if (fu) for (const p of o.f) {
    const t = fTiles(fu.fs, p[0], p[1], p[2]), [mx, my] = fMaster(fu.fs, t);
    for (let y = 0; y < t.length; y++) for (let x = 0; x < t[y].length; x++) { const k = t[y][x]; if (k != null && fu.fs.tileTypes[k].availability !== 'ROOM') d[(p[4] + y - o.y + 1) * w + p[3] + x - o.x + 1] |= 8; }
    d[(p[4] + my - o.y + 1) * w + p[3] + mx - o.x + 1] |= (fItemId(fu.fs, p[0], p[1], p[2]) + 1) << 4;
  } }
  if (fx) { for (let y = 0; y < fx.h; y++) for (let x = 0; x < fx.w; x++) if (fx.grid[y][x] === 'S' || fx.grid[y][x] === '#') d[(y + 1) * w + x + 1] |= 8; d[(fx.my + 1) * w + fx.mx + 1] |= (fx.id + 1) << 4; }
  if (hc) { const g = houseGrid(hc.fit.bi, hc.fit.n, hc.fit.rot); for (let y = 0; y < g.length; y++) for (let x = 0; x < g[0].length; x++) if (g[y][x] === 'x') d[(y + 1) * w + x + 1] |= 8; d[w + 1] |= (hc.fit.id + 1) << 4; }
  const key = o.t.toUpperCase();
  // Rezept (seit Version 28): Better Blueprints setzt RECIPE_INDEX beim Platzieren über setIndustry(), wenn das Rezept freigeschaltet ist; Reihenfolge = INDUSTRIES der Raumdatei
  const bb = BT.get(o.t), rIdx = isProd(o.t) && bb?.rc?.length > 1 ? Math.max(0, Math.min(bb.rc.length - 1, o.p?.rc ?? 0)) : 0;
  return new JE().str('NAME', BT.get(o.t)?.n || key).str('MODE', 'ROOM').raw('ROOM', key).raw('STRUCTURE', '_').raw('CHECK', '0').raw('WIDTH', w).raw('HEIGHT', h).ints('DATA', d).raw('UPGRADE', roomUp(o)).raw('RECIPE_INDEX', rIdx);
}
async function expBuild(ex, name, floor) {
  const r = ex.r;
  const rooms = ex.rooms.map(({ o, hc, fx }) => new JE().raw('OX', o.x - 1 - r.x).raw('OY', o.y - 1 - r.y).obj('PRINT', roomPrint(o, hc, fx)));
  const jobs = [...ex.roads.map(([x, y]) => new JE().raw('OX', x).raw('OY', y).str('KEY', 'JOB_ROAD_' + floor)), ...ex.walls.map(([x, y]) => new JE().raw('OX', x).raw('OY', y).str('KEY', WALL_JOB)), ...(ex.ceils || []).map(([x, y]) => new JE().raw('OX', x).raw('OY', y).str('KEY', CEIL_JOB))];
  const json = new JE().str('NAME', name).str('MODE', 'AREA').raw('WIDTH', r.w).raw('HEIGHT', r.h).objs('AREA_ROOMS', rooms).objs('AREA_JOBS', jobs).toString();
  const buf = await new Response(new Blob([new TextEncoder().encode(json)]).stream().pipeThrough(new CompressionStream('deflate'))).arrayBuffer();
  const by = new Uint8Array(buf); let bin = ''; for (let i = 0; i < by.length; i += 0x8000) bin += String.fromCharCode.apply(null, by.subarray(i, i + 0x8000));
  const meta = `[Name:${(name || '?').replace(/\s+/g, '_').replace(/[\[\]:;"]/g, '_')};Category:AREA;Size:${r.w}x${r.h};Slots:0]:`;
  return 'SYX:BB' + meta + btoa(bin);
}
// ---------- Import von Better-Blueprints-Zeilen (seit Version 29, Feature E) ----------
// Zeile "SYX:BB[Meta]:" + Base64(zlib(Text im Json-Format des Spiels)), wie BBPrintCodec.importFromString.
// Bereich (MODE AREA: AREA_ROOMS mit OX/OY/PRINT, AREA_JOBS) oder einzelner Raum (MODE ROOM). Ergebnis: Stempel-Vorlage wie beim Kopieren (V).
// DATA je Kachel (SavedPrint): 1 Raum, 2 Wand (Ring), 4 auf Raumkacheln „überdacht“, auf Ringkacheln Tür, 8 blockiert, (Möbel-Index + 1) << 4 am Master.
async function bbDecodeLine(line) {
  let s = String(line || '').trim();
  if (s.length >= 2 && s[0] === '"' && s[s.length - 1] === '"') s = s.slice(1, -1).trim();
  if (!s.startsWith('SYX:BB')) throw new Error('This is not a Better Blueprints line. It starts with “SYX:BB”.');
  let rest = s.slice(6).trim();
  if (rest.startsWith('[')) { const m = rest.lastIndexOf(']:'); if (m >= 0 && m + 2 < rest.length) rest = rest.slice(m + 2).trim(); }
  let bin;
  try { bin = atob(rest.replace(/[^A-Za-z0-9+/=]/g, '')); } catch { throw new Error('The line is damaged (Base64). Please paste the complete line.'); }
  const by = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) by[i] = bin.charCodeAt(i);
  if (typeof DecompressionStream !== 'function') throw new Error('This browser cannot unpack the line.');
  try { return new TextDecoder().decode(await new Response(new Blob([by]).stream().pipeThrough(new DecompressionStream('deflate'))).arrayBuffer()); }
  catch { throw new Error('The line is incomplete or damaged. Please paste the complete line.'); }
}
// Json-Format des Spiels (snake2d Json): KEY: Wert, … ; Werte sind {…}, […], "Text" oder ein Wort/Zahl bis zum Komma
function sosParse(txt) {
  let i = 0; const n = txt.length;
  const ws = () => { while (i < n && /[\s,]/.test(txt[i])) i++; };
  function val() {
    ws(); const c = txt[i];
    if (c === '{') { i++; return obj('}'); }
    if (c === '[') { i++; const a = []; for (;;) { ws(); if (i >= n) throw new Error('list not closed'); if (txt[i] === ']') { i++; return a; } a.push(val()); } }
    if (c === '"') { const e = txt.indexOf('"', i + 1); if (e < 0) throw new Error('text not closed'); const v = txt.slice(i + 1, e); i = e + 1; return v; }
    let e = i; while (e < n && !/[,\r\n\]}]/.test(txt[e])) e++;
    const w = txt.slice(i, e).trim(); i = e; return /^-?\d+(\.\d+)?$/.test(w) ? +w : w;
  }
  function obj(end) {
    const o = {};
    for (;;) {
      ws(); if (i >= n) { if (end) throw new Error('object not closed'); return o; }
      if (txt[i] === end) { i++; return o; }
      const k = txt.indexOf(':', i); if (k < 0) throw new Error('key without value');
      const key = txt.slice(i, k).trim().replace(/^"(.*)"$/, '$1'); i = k + 1; o[key] = val();   // auch echtes JSON (Schlüssel in Anführungszeichen)
    }
  }
  return obj(null);
}
// Räume, die im Spiel je Kachel ein einzelnes festes Stück tragen (Kanal: DATA 41 = Raum + blockiert + Stück 1); der Planer braucht dafür keine Möbeldaten
const ONE_PIECE = new Set(['_watercanal']);
function fItemOf(fs, idx) { let off = 1; for (let g = 0; g < fs.groups.length; g++) { const G = fs.groups[g], m = G.items.length * (G.rotations + 1); if (idx < off + m) { const k = idx - off; return [g, Math.floor(k / (G.rotations + 1)), k % (G.rotations + 1)]; } off += m; } return null; }
// Spiel-Blueprint → Vorlage { n, s, w, h, ter, cl, b } plus Bericht, was nicht mitkam
function bbToTpl(J) {
  const area = J.MODE === 'AREA' || 'AREA_ROOMS' in J || 'AREA_JOBS' in J;
  const prints = area ? (Array.isArray(J.AREA_ROOMS) ? J.AREA_ROOMS : []).map(r => ({ ox: +r.OX || 0, oy: +r.OY || 0, P: r.PRINT || {} })) : [{ ox: 0, oy: 0, P: J }];
  const jobs = area && Array.isArray(J.AREA_JOBS) ? J.AREA_JOBS.map(j => ({ x: +j.OX || 0, y: +j.OY || 0, k: String(j.KEY ?? '').trim().replace(/^"|"$/g, '').toUpperCase() })) : [];
  const rep = { rooms: 0, homes: 0, furn: 0, unknown: new Map(), bad: [], upg: 0, upgOk: 0, rc: 0, fLost: 0, noFurn: 0, fLostT: new Map(), noFurnT: new Map(), otherJobs: new Map() };
  const R = [];
  for (const { ox, oy, P } of prints) {
    const key = String(P.ROOM ?? ''), t = key.toLowerCase(), w = +P.WIDTH || 0, h = +P.HEIGHT || 0, d = Array.isArray(P.DATA) ? P.DATA.map(v => +v || 0) : [];
    const nm = BT.get(t)?.n || key || '?';
    if (!BT.has(t)) { rep.unknown.set(key || '?', (rep.unknown.get(key || '?') || 0) + 1); continue; }
    if (!w || !h || d.length !== w * h) { rep.bad.push(`${nm}: tile data incomplete`); continue; }
    const cells = [], ring = [], doors = [], anchors = [];
    d.forEach((v, j) => {
      const x = ox + j % w, y = oy + ((j / w) | 0);
      if (v & 1) cells.push([x, y]); else { if (v & 6) ring.push([x, y]); if (v & 4) doors.push([x, y]); }
      if (v >> 4) anchors.push([x, y, (v >> 4) - 1]);
    });
    if (!cells.length) { rep.bad.push(`${nm}: no room tiles`); continue; }
    const xs = cells.map(c => c[0]), ys = cells.map(c => c[1]);
    const x0 = Math.min(...xs), y0 = Math.min(...ys), bw = Math.max(...xs) - x0 + 1, bh = Math.max(...ys) - y0 + 1;
    let mask = null;
    if (cells.length !== bw * bh) { const a = new Uint8Array(bw * bh); for (const [x, y] of cells) a[(y - y0) * bw + x - x0] = 1; mask = bitsEncode(a); }
    let v = null, f = null;
    const L = fxList(t);
    if (L) {
      const q = anchors.length === 1 ? L.find(z => z.id === anchors[0][2]) : null;
      if (q && q.w === bw && q.h === bh && !mask) v = [q.g, q.s, q.r];
      else rep.bad.push(`${nm} at ${x0}, ${y0}: size ${bw} × ${bh} or furniture piece does not match the game, marked red in the planner`);
    } else if (anchors.length && !ONE_PIECE.has(t)) {
      const fu = furnOf(t);
      if (!fu) { rep.noFurn += anchors.length; rep.noFurnT.set(nm, (rep.noFurnT.get(nm) || 0) + anchors.length); }
      else {
        const inside = new Set(cells.map(([x, y]) => x + ',' + y));
        f = [];
        for (const [ax, ay, idx] of anchors) {
          const it = fItemOf(fu.fs, idx); if (!it) { rep.fLost++; rep.fLostT.set(nm, (rep.fLostT.get(nm) || 0) + 1); continue; }
          const tl = fTiles(fu.fs, ...it), [mx, my] = fMaster(fu.fs, tl), px = ax - mx, py = ay - my;
          let ok = true; for (let yy = 0; yy < tl.length && ok; yy++) for (let xx = 0; xx < tl[yy].length; xx++) if (tl[yy][xx] != null && !inside.has((px + xx) + ',' + (py + yy))) { ok = false; break; }
          if (ok) f.push([...it, px, py]); else { rep.fLost++; rep.fLostT.set(nm, (rep.fLostT.get(nm) || 0) + 1); }
        }
        rep.furn += f.length; if (!f.length) f = null;
      }
    }
    let pp = null;
    const rc = Math.max(0, +P.RECIPE_INDEX || 0), bb = BT.get(t);
    if (rc && isProd(t) && bb.rc?.length > 1 && rc < bb.rc.length) { pp = { rc }; rep.rc++; }
    const upg = Math.max(0, Math.round(+P.UPGRADE || 0)); if (upg) { if (upg <= upMax(t)) { pp = { ...(pp || {}), up: upg }; rep.upgOk++; } else rep.upg++; }
    rep.rooms++; if (t === '_home') rep.homes++;
    R.push({ t, x: x0, y: y0, w: bw, h: bh, doors, mask, v, f, pp, all: [...cells, ...ring] });
  }
  // Kanäle: im Spiel ist jede Kanalkachel ein eigener Raum mit genau einem Kanalstück; der Planer fasst benachbarte Kacheln zu einem Kanal zusammen
  for (const t of ONE_PIECE) {
    const parts = R.filter(r => r.t === t && !r.mask && r.w === 1 && r.h === 1 && !r.doors.length && !r.pp); if (parts.length < 2) continue;
    const rest = R.filter(r => !parts.includes(r)), pos = new Map(parts.map(r => [r.x + ',' + r.y, r])), seen = new Set();
    for (const r0 of parts) {
      const k0 = r0.x + ',' + r0.y; if (seen.has(k0)) continue;
      const comp = [], q = [r0]; seen.add(k0);
      while (q.length) { const r = q.pop(); comp.push([r.x, r.y]); for (const [dx, dy] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) { const k = (r.x + dx) + ',' + (r.y + dy); if (pos.has(k) && !seen.has(k)) { seen.add(k); q.push(pos.get(k)); } } }
      const x0 = Math.min(...comp.map(c => c[0])), y0 = Math.min(...comp.map(c => c[1])), bw = Math.max(...comp.map(c => c[0])) - x0 + 1, bh = Math.max(...comp.map(c => c[1])) - y0 + 1;
      let mask = null; if (comp.length !== bw * bh) { const a = new Uint8Array(bw * bh); for (const [x, y] of comp) a[(y - y0) * bw + x - x0] = 1; mask = bitsEncode(a); }
      rest.push({ t, x: x0, y: y0, w: bw, h: bh, doors: [], mask, v: null, f: null, pp: null, all: comp });
    }
    rep.rooms -= parts.length - (rest.length - (R.length - parts.length)); R.length = 0; R.push(...rest);
  }
  // Rahmen wie BBAreaBlueprintNormalizer: angegebene Größe, bei Inhalt außerhalb erweitert und verschoben
  let mnx = 0, mny = 0, mxx = Math.max(0, (area ? +J.WIDTH || 0 : 0) - 1), mxy = Math.max(0, (area ? +J.HEIGHT || 0 : 0) - 1), any = false;
  const grow = (x, y) => { mnx = Math.min(mnx, x); mny = Math.min(mny, y); mxx = Math.max(mxx, x); mxy = Math.max(mxy, y); any = true; };
  for (const r of R) for (const [x, y] of r.all) grow(x, y);
  for (const j of jobs) grow(j.x, j.y);
  if (!area && R.length) { mnx = Math.min(...R[0].all.map(p => p[0])); mny = Math.min(...R[0].all.map(p => p[1])); mxx = Math.max(...R[0].all.map(p => p[0])); mxy = Math.max(...R[0].all.map(p => p[1])); }
  if (!any && !R.length) return { T: null, rep };
  const fw = mxx - mnx + 1, fh = mxy - mny + 1;
  // Straßen, Mauern, Decken; nichts auf Raum- oder Wandringkacheln (Mud-Decken auf Türen, Wand-Aufträge am Ring)
  const taken = new Set(); for (const r of R) for (const [x, y] of r.all) taken.add((x - mnx) + ',' + (y - mny));
  const TER = new Uint8Array(fw * fh), CL = new Uint8Array(fw * fh);
  for (const j of jobs) {
    const x = j.x - mnx, y = j.y - mny, k = y * fw + x; if (taken.has(x + ',' + y)) continue;
    if (/^(JOB_)?ROAD_/.test(j.k)) { if (TER[k] !== 2) TER[k] = 1; }
    else if (/^JOB_WALL_/.test(j.k)) TER[k] = 2;
    else if (/^JOB_CEILING_/.test(j.k)) CL[k] = 1;
    else rep.otherJobs.set(j.k, (rep.otherJobs.get(j.k) || 0) + 1);
  }
  for (let k = 0; k < fw * fh; k++) if (TER[k] === 2) CL[k] = 0;
  const ter = [], cl = [];
  for (let y = 0; y < fh; y++) for (const [A, val, out] of [[TER, 1, ter], [TER, 2, ter], [CL, 1, cl]]) {
    let x = 0; while (x < fw) { if (A[y * fw + x] !== val) { x++; continue; } let e = x; while (e < fw && A[y * fw + e] === val) e++; out.push(out === ter ? [val, x, y, e - x, 1] : [x, y, e - x, 1]); x = e; }
  }
  const b = R.map(r => [r.t, r.x - mnx, r.y - mny, r.w, r.h, r.doors.map(([x, y]) => [x - mnx, y - mny]), r.mask, r.v, r.f ? r.f.map(([g, s, q, x, y]) => [g, s, q, x - mnx, y - mny]) : null, r.pp]);
  const name = String(J.NAME || (area ? 'Area' : BT.get(R[0]?.t)?.n) || 'Import').slice(0, 60);
  return { T: { id: 'bbimp', n: name, s: 'From Better Blueprints', w: fw, h: fh, ter, cl, b }, rep, area };
}
function bbReport(T, rep) {
  const nT = T ? T.ter.filter(e => e[0] === 1).reduce((a, e) => a + e[3] * e[4], 0) : 0, nM = T ? T.ter.filter(e => e[0] === 2).reduce((a, e) => a + e[3] * e[4], 0) : 0, nC = T ? T.cl.reduce((a, e) => a + e[2] * e[3], 0) : 0;
  const ok = [`${rep.rooms} ${rep.rooms === 1 ? 'room' : 'rooms'}${rep.homes ? `, of which ${rep.homes} house rows` : ''}`];
  if (rep.furn) ok.push(`${rep.furn} furniture`); if (rep.rc) ok.push(`${rep.rc} with recipe`); if (rep.upgOk) ok.push(`${rep.upgOk} with upgrade level`);
  if (nT) ok.push(`${nT} road tiles`); if (nM) ok.push(`${nM} free wall tiles`); if (nC) ok.push(`${nC} ceilings`);
  const warn = [];
  if (rep.unknown.size) warn.push(`Skipped, unknown to the planner: ${[...rep.unknown].map(([k, c]) => c > 1 ? `${k} (${c}×)` : k).join(', ')}.`);
  for (const s of rep.bad.slice(0, 5)) warn.push(s + '.'); if (rep.bad.length > 5) warn.push(`… and ${rep.bad.length - 5} more rooms with problems.`);
  const byT = m => [...m].map(([k, c]) => `${k} ${c}`).join(', ');
  if (rep.fLost) warn.push(`${rep.fLost} furniture pieces could not be matched and are missing (${byT(rep.fLostT)}).`);
  if (rep.noFurn) warn.push(`${rep.noFurn} furniture pieces in rooms the planner cannot furnish are missing (${byT(rep.noFurnT)}).`);
  if (rep.otherJobs.size) warn.push(`Other build orders are missing: ${[...rep.otherJobs].map(([k, c]) => `${k} (${c}×)`).join(', ')}.`);
  if (rep.upg) warn.push(`${rep.upg} ${rep.upg === 1 ? 'room had' : 'rooms had'} an upgrade level that does not exist for this room.`);
  if (T && (T.w > W || T.h > H)) warn.push(`The area is ${T.w} × ${T.h} large, the map only ${W} × ${H}. Enlarge the map at the top to place it.`);
  return { ok: ok.join(', '), warn };
}
let bbLast = null;
async function bbImport(line) {
  const txt = await bbDecodeLine(line);
  let J; try { J = sosParse(txt); } catch (e) { throw new Error('The content of the line could not be read (' + e.message + ').'); }
  const res = bbToTpl(J);
  if (!res.T || (!res.T.b.length && !res.T.ter.length && !res.T.cl.length)) throw new Error('The line contains nothing the planner can place.' + (res.rep.unknown.size ? ` Unknown: ${[...res.rep.unknown.keys()].join(', ')}.` : ''));
  return res;
}
const bbBox = document.getElementById('bbBox'), bbInfo = document.getElementById('bbInfo');
function bbShow(res) {
  const { ok, warn } = bbReport(res.T, res.rep);
  bbInfo.hidden = false;
  bbInfo.innerHTML = `<p class="muted"><b>“${esc(res.T.n)}”</b> · ${res.T.w} × ${res.T.h}: ${esc(ok)}.</p>${warn.map(s => `<p class="muted" style="color:var(--warn,var(--bad))">${esc(s)}</p>`).join('')}
    <p class="muted">Click places the area, R rotates, Esc ends. You choose road paving and wall material in the game again.</p>
    <div class="row"><button class="btn sm" id="bbStamp">Stamp again</button><button class="btn sm" id="bbCap">Save as template</button></div>`;
  document.getElementById('bbStamp').addEventListener('click', () => { if (bbLast) pickTpl(bbLast); });
  document.getElementById('bbCap').addEventListener('click', () => {
    if (!bbLast) return; const { w, h, ter, cl, b } = bbLast; pendingCap = { w, h, ter, cl, b }; showCapForm();
    const nm = document.getElementById('capName'); if (nm) nm.value = bbLast.n;
    document.getElementById('capForm').scrollIntoView({ block: 'nearest' });
  });
}
// ---------- Sammel-Import (seit Version 33): ganze Better-Blueprints-Datei ----------
// AreaBlueprints.json (Mod-Ordner, BBAreaBlueprintStore): BLUEPRINTS: [{ BP_STRING: "SYX:BB…" }, …]
// SavedPrints (Profil des Spiels, SavedPrints.save): BLUEPRINTS: [{ NAME, MODE ROOM, ROOM, WIDTH, HEIGHT, DATA, UPGRADE, RECIPE_INDEX }, …]
// Außerdem: beliebiger Text mit mehreren SYX:BB-Zeilen. Alles wird zu eigenen Vorlagen in einer Kategorie.
const looksBulk = s => /BLUEPRINTS/.test(s) || (s.match(/SYX:BB/g) || []).length > 1;
async function bbBulk(text) {
  const s = String(text || '').replace(/^﻿/, ''), items = [];
  if (/BLUEPRINTS/.test(s)) {
    let J; try { J = JSON.parse(s); } catch { try { J = sosParse(s); } catch (e) { throw new Error('The file could not be read (' + e.message + ').'); } }   // echtes JSON oder Spielformat (JsonE)
    const L = Array.isArray(J.BLUEPRINTS) ? J.BLUEPRINTS : [];
    if (!L.length) throw new Error('There are no blueprints in the file.');
    for (const [k, e] of L.entries()) {
      const nm = String(e?.NAME || '').trim();
      try {
        if (e && typeof e.BP_STRING === 'string') { const r = await bbImport(e.BP_STRING); items.push({ ok: true, kind: r.area ? 'Area' : 'Room', ...r }); }
        else if (e && typeof e === 'object' && (e.ROOM || e.AREA_ROOMS || e.AREA_JOBS)) { const r = bbToTpl(e); if (!r.T || (!r.T.b.length && !r.T.ter.length && !r.T.cl.length)) throw new Error('nothing the planner can place' + (r.rep.unknown.size ? ` (unknown: ${[...r.rep.unknown.keys()].join(', ')})` : '')); items.push({ ok: true, kind: r.area ? 'Area' : 'Room', ...r }); }
        else throw new Error('unknown entry');
      } catch (err) { items.push({ ok: false, n: nm || `Entry ${k + 1}`, err: err.message }); }
    }
  } else {
    const L = s.match(/SYX:BB[^\s"',]*/g) || [];
    if (!L.length) throw new Error('No Better Blueprints lines found.');
    for (const [k, line] of L.entries()) { try { const r = await bbImport(line); items.push({ ok: true, kind: r.area ? 'Area' : 'Room', ...r }); } catch (err) { items.push({ ok: false, n: `Line ${k + 1}`, err: err.message }); } }
  }
  return items;
}
let bulkLast = null;
function bulkShow(items) {
  bulkLast = items; bbInfo.hidden = false;
  const ok = items.filter(x => x.ok), bad = items.filter(x => !x.ok), nA = ok.filter(x => x.kind === 'Area').length;
  const warnN = ok.filter(x => bbReport(x.T, x.rep).warn.length).length;
  bbInfo.innerHTML = `<p class="muted"><b>${items.length} blueprints read:</b> ${nA} ${nA === 1 ? 'Area' : 'Areas'}, ${ok.length - nA} ${ok.length - nA === 1 ? 'Room' : 'Rooms'}${bad.length ? `, <span style="color:var(--bad)">${bad.length} unreadable</span>` : ''}${warnN ? `, ${warnN} with notes` : ''}.</p>
    <div class="row"><label class="muted" for="bulkCat">Category</label><input type="text" id="bulkCat" maxlength="40" value="Better Blueprints" style="flex:1;min-width:0"></div>
    <div class="row"><button class="btn primary sm" id="bulkSave"${ok.length ? '' : ' disabled aria-disabled="true"'}>Save all as templates</button></div>
    <div class="bulklist">${items.map((x, i) => x.ok ? `<div class="row"><span class="nm" title="${esc(bbReport(x.T, x.rep).warn.join(' '))}">${esc(x.T.n)} <small class="muted">${x.kind} · ${x.T.w}×${x.T.h}${bbReport(x.T, x.rep).warn.length ? ' · note' : ''}</small></span><button class="btn sm" data-bi="${i}">Stamp</button></div>` : `<div class="row"><span class="nm" style="color:var(--bad)">${esc(x.n)}: ${esc(x.err)}</span></div>`).join('')}</div>`;
  bbInfo.querySelectorAll('[data-bi]').forEach(b => b.addEventListener('click', () => { const x = items[+b.dataset.bi]; bbLast = x.T; pickTpl(x.T); }));
  document.getElementById('bulkSave')?.addEventListener('click', () => { const r = bulkSave(items, document.getElementById('bulkCat').value); toast(r.msg); });
}
function bulkSave(items, cat) {
  const c = String(cat || '').trim().slice(0, 40) || 'Better Blueprints', mine = mineList(), sigs = new Set(mine.map(T => tplSig({ ...T, cl: T.cl || [] }))), names = new Set(mine.map(T => T.n));
  let n = 0, dup = 0; const add = [];
  for (const [k, x] of items.entries()) {
    if (!x.ok) continue;
    const { w, h, ter, cl, b } = x.T, sg = tplSig({ w, h, ter, cl, b });
    if (sigs.has(sg)) { dup++; continue; }
    let nm = x.T.n || 'Blueprint', i = 2; while (names.has(nm)) nm = `${x.T.n} (${i++})`;
    names.add(nm); sigs.add(sg); add.push({ id: 'c' + Date.now() + '_' + k, n: nm, s: `From Better Blueprints · ${x.kind}`, c, w, h, ter, cl, b }); n++;
  }
  if (n && !mineSave([...mine, ...add])) return { n: 0, dup, msg: 'Saving failed: the browser storage is full or blocked. Load fewer blueprints at once or delete old templates.' };
  if (n) { catToggle(c, true); refreshTpls(); }
  return { n, dup, msg: n ? `${n} ${n === 1 ? 'template' : 'templates'} in “${c}” saved${dup ? `, ${dup} already there` : ''}.` : dup ? `All ${dup} already exist as templates.` : 'Nothing to save.' };
}
async function bbLoadText(text) {
  try {
    if (looksBulk(text)) { const items = await bbBulk(text); bulkShow(items); toast(`${items.filter(x => x.ok).length} of ${items.length} blueprints read. Below: “Save all as templates”.`); return; }
    const res = await bbImport(text); bbLast = res.T; bbShow(res); pickTpl(res.T);
    toast(`“${res.T.n}” (${res.T.w} × ${res.T.h}) is ready: click to place, R rotates.`);
  } catch (e) { bbInfo.hidden = false; bbInfo.innerHTML = `<p class="muted" style="color:var(--bad)">${esc(e.message || 'The line could not be read.')}</p>`; toast(e.message || 'The line could not be read.'); }
}
document.getElementById('bbLoad').addEventListener('click', () => bbLoadText(bbBox.value));
const bbFile = document.getElementById('bbFile');
bbFile.addEventListener('change', async () => { const f = bbFile.files[0]; bbFile.value = ''; if (!f) return; if (f.size > 20e6) { toast('The file is too large (over 20 MB).'); return; } await bbLoadText(await f.text()); });
function openExport(r) {
  expData = expCollect(r);
  const ex = expData, nH = ex.rooms.filter(x => x.o.t === '_home').length, nHU = ex.rooms.reduce((s, x) => s + (x.o.t === '_home' && x.fx ? x.fx.s + 1 : 0), 0);
  const blocked = ex.problems.length > 0, empty = !ex.rooms.length && !ex.roads.length && !ex.walls.length && !ex.ceils.length;
  expBody.innerHTML = `
    <dl class="kv"><dt>Area</dt><dd>${r.w} × ${r.h} tiles, from ${r.x}, ${r.y}</dd><dt>Rooms</dt><dd>${ex.rooms.length}${nH ? `, of which ${nH} house rows with ${nHU} houses` : ''}${ex.rooms.some(x => x.fx && x.o.t !== '_home') ? `, ${ex.rooms.filter(x => x.fx && x.o.t !== '_home').length} with fixed size` : ''}</dd>${ex.rooms.some(x => x.o.f?.length) ? `<dt>Furnished</dt><dd>${ex.rooms.filter(x => x.o.f?.length).length} rooms, ${ex.rooms.reduce((a, x) => a + (x.o.f?.length || 0), 0)} furniture</dd>` : ''}<dt>Road tiles</dt><dd>${ex.roads.length}</dd><dt>Free wall tiles</dt><dd>${ex.walls.length}</dd>${ex.ceils.length ? `<dt>Ceilings</dt><dd>${ex.ceils.length}</dd>` : ''}</dl>
    ${blocked ? `<div><p class="muted" style="color:var(--bad)"><b>Export blocked.</b> These rooms do not match the game:</p><ul class="muted" style="margin:4px 0 0 18px;padding:0">${ex.problems.map(p => `<li>${esc(BT.get(p.o.t)?.n || p.o.t)} at ${p.o.x}, ${p.o.y} (${p.o.w} × ${p.o.h}): ${esc(p.msg)}</li>`).join('')}</ul><div class="row" style="margin-top:6px"><button class="btn sm" id="expShow">Select the first room</button></div></div>` : ''}
    ${empty ? '<p class="muted" style="color:var(--bad)">There is nothing inside the frame that can be exported.</p>' : ''}
    ${ex.notes.map(n => `<p class="muted">${esc(n)}</p>`).join('')}
    <div class="grid3" style="grid-template-columns:2fr 1fr"><label for="expName">Name in the game<input type="text" id="expName" value="${esc(isSampleName(planName) ? 'District' : planName)}"></label>
    <label for="expFloor">Road paving<select id="expFloor">${EXP_FLOORS.map(([k, n]) => `<option value="${k}"${k === expFloor ? ' selected' : ''}>${esc(n)}</option>`).join('')}</select></label></div>
    <div class="row"><button class="btn primary" id="expGo"${blocked || empty ? ' aria-disabled="true" disabled' : ''}>Create and copy line</button><button class="btn" id="expClose">Close</button></div>
    <textarea id="expOut" readonly aria-label="Blueprint line for the game" placeholder="The line for the mod appears here"></textarea>
    <p class="muted">In the game: open Better Blueprints, “Import blueprint from clipboard string”, then place it. For wall rings and free walls switch on the wall option in the mod, you choose the material there. Houses, fixed-size rooms and furnished rooms bring their furniture, supports come as wall tiles. Rooms that are not furnished you furnish in the game.</p>`;
  expDlg.hidden = false;
  document.getElementById('expClose').addEventListener('click', () => { expDlg.hidden = true; });
  document.getElementById('expShow')?.addEventListener('click', () => { const o = ex.problems[0].o; selU = o.u; computeSelReach(); expDlg.hidden = true; setTool('sel'); refreshPanels(); z = Math.max(z, 8); ox = vw / 2 - (o.x + o.w / 2) * z; oy = vh / 2 - (o.y + o.h / 2) * z; schedule(); });
  document.getElementById('expFloor').addEventListener('change', e => { expFloor = e.target.value; try { localStorage.setItem('syx-bezirk-floor', expFloor); } catch { /* egal */ } });
  document.getElementById('expGo').addEventListener('click', async () => {
    if (blocked || empty) return;
    const out = document.getElementById('expOut');
    try {
      const str = await expBuild(ex, document.getElementById('expName').value.trim() || 'District', expFloor); out.value = str;
      try { await navigator.clipboard.writeText(str); toast(`Line copied (${str.length.toLocaleString('en-US')} characters). Import it in the game via Better Blueprints.`); }
      catch { out.focus(); out.select(); toast('The line is in the field and selected. Copy it with Ctrl+C.'); }
    } catch { toast('The line could not be created in this browser.'); }
  });
}
expDlg.addEventListener('click', e => { if (e.target === expDlg) expDlg.hidden = true; });

// ---------- Einrichtungs-Editor ----------
const furnDlg = document.getElementById('furnDlg'), fcv = document.getElementById('furnCv'), fx2 = fcv.getContext('2d'), fStage = document.getElementById('furnStage');
const fHint = document.getElementById('furnHint'), fGroups = document.getElementById('furnGroups'), fStatsEl = document.getElementById('furnStats');
let ed = null;   // { u, fu, sel:{g,s,r}|null, hov:{c,r}|null, cx, z, ox, oy }
const grpCol = (g, n, l = 52) => `hsl(${Math.round((g * 360 / Math.max(1, n)) + 35) % 360} 55% ${l}%)`;
function edObj() { return ed ? blds.get(ed.u) : null; }
function openFurnish(o) {
  const fu = furnOf(o.t);
  if (!fu) { toast('There is no furnishing for this building in the game.'); return; }
  if (o.w * o.h > 60 * 60) { toast('The room is too large for the editor (at most 60 × 60 tiles outline).'); return; }
  ed = { u: o.u, fu, sel: null, hov: null, cx: null, mode: 'furn' };
  furnDlg.hidden = false; edModeBtns(); edSync(); requestAnimationFrame(edResize);
}
function closeFurnish() { furnDlg.hidden = true; ed = null; refreshPanels(); schedule(); }
function edSync() {
  const o = edObj(); if (!o) { closeFurnish(); return; }
  ed.cx = fCtx(o, ed.fu);
  const nh = isWalled(o.t) ? edHoles(ed.cx).size : 0, form = o.cells.length + nh < o.w * o.h;
  document.getElementById('furnTitle').textContent = `Furnish ${BT.get(o.t)?.n || o.t} · ${o.w} × ${o.h}${nh ? ` · ${nh} ${nh === 1 ? 'support' : 'supports'}` : ''}${form ? ' (free shape)' : ''}`;
  edGroups(); edStats(); edDraw(); edHint();
}
const ED_MODES = [['furn', 'Furniture', 'D'], ['room', 'Room', 'F'], ['door', 'Door', 'W'], ['pillar', 'Support', 'S']];
const ED_VM = 4;   // Rand um den Raum in Kacheln: Platz zum Vergrößern, zeigt Nachbarn, Straßen und Mauern
function edModeBtns() {
  const o = edObj(), walled = o && isWalled(o.t), box = document.getElementById('furnModes');
  box.innerHTML = ED_MODES.map(([k, n, key]) => `<button class="btn sm${ed.mode === k ? ' on' : ''}" data-m="${k}"${(k === 'door' || k === 'pillar') && !walled ? ' disabled aria-disabled="true" title="Only for rooms with a wall"' : ` title="${n} (${key})"`}>${n} <kbd>${key}</kbd></button>`).join('');
  box.querySelectorAll('button').forEach(b => b.addEventListener('click', () => edSetMode(b.dataset.m)));
}
function edSetMode(m) {
  const o = edObj(); if ((m === 'door' || m === 'pillar') && !isWalled(o.t)) { toast('Doors and supports exist only for rooms with a wall.'); return; }
  ed.mode = m; if (m !== 'furn') ed.sel = null; edModeBtns(); edGroups(); edDraw(); edHint();
}
// Stützen = Nicht-Raum-Kacheln, die vom Rand aus nicht erreichbar sind (Löcher im Raum)
function edHoles(cx) {
  const { gridW: gw, gridH: gh, room } = cx, seen = new Uint8Array(gw * gh), st = [];
  for (let r = 0; r < gh; r++) for (let c = 0; c < gw; c++) if ((r === 0 || c === 0 || r === gh - 1 || c === gw - 1) && !room[r][c]) { seen[r * gw + c] = 1; st.push(r * gw + c); }
  while (st.length) { const k = st.pop(), r = (k / gw) | 0, c = k % gw; for (const [dr, dc] of [[1,0],[-1,0],[0,1],[0,-1]]) { const nr = r + dr, nc = c + dc; if (nr < 0 || nc < 0 || nr >= gh || nc >= gw || room[nr][nc] || seen[nr * gw + nc]) continue; seen[nr * gw + nc] = 1; st.push(nr * gw + nc); } }
  const out = new Set(); for (let r = 0; r < gh; r++) for (let c = 0; c < gw; c++) if (!room[r][c] && !seen[r * gw + c]) out.add(r * gw + c);
  return out;
}
// Deckenstütze: Raumkachel herausnehmen (das Spiel setzt dort eine Wand, die das Dach trägt) oder Stütze wieder entfernen
function edPillar(t) {
  const o = edObj(), cx = ed.cx, mi = (o.y - 1 + t.r) * W + o.x - 1 + t.c;
  if (cx.room[t.r]?.[t.c]) {
    if (cx.occupancy[t.r][t.c] >= 0) { toast('A furniture piece stands there. Remove it first (right click).'); return; }
    const nc = o.cells.filter(i => i !== mi);
    if (!nc.length || components(nc).length > 1) { toast('A support here would split the room.'); return; }
    commit(); reshape(o, nc, o.d); dirty(); edSync(); return;
  }
  if (edHoles(cx).has(t.r * cx.gridW + t.c) && wcnt[mi] === 1 && !o.d.includes(mi) && terr[mi] !== 2) {
    const nc = [...o.cells, mi]; if (!fitsCells(o.t, nc, [o])) { toast('The tile cannot be taken back into the room.'); return; }
    commit(); reshape(o, nc, o.d); dirty(); edSync(); return;
  }
  toast('Put supports on room tiles, preferably on the yellow ones. Clicking a support removes it again.');
}
function edDoor(t) {
  const o = edObj(), mi = (o.y - 1 + t.r) * W + o.x - 1 + t.c;
  if (!o._ring.has(mi) || ed.cx.room[t.r]?.[t.c]) { toast('Doors go into the wall ring.'); return; }
  if (!o.d.includes(mi) && !validDoor(o, mi)) { toast('Doors go into the wall ring, not into the corner.'); return; }
  commit(); reshape(o, o.cells, o.d.includes(mi) ? o.d.filter(i => i !== mi) : [...o.d, mi]); dirty(); edSync();
}
function edResize() { if (!ed) return; const r = fStage.getBoundingClientRect(), d = window.devicePixelRatio || 1; fcv.width = Math.max(1, Math.round(r.width * d)); fcv.height = Math.max(1, Math.round(r.height * d)); edDraw(); }
new ResizeObserver(edResize).observe(fStage);
function edGroups() {
  const o = edObj(), { fs, P } = ed.fu, n = fs.groups.length;
  fGroups.innerHTML = fs.groups.map((G, g) => {
    const cnt = o.f.filter(p => p[0] === g).length, low = cnt < (G.min || 0), high = G.max != null && cnt > G.max;
    const lim = G.max != null && G.max < 1e6 ? `${cnt} / ${G.min ? G.min + '–' : ''}${G.max}` : G.min ? `${cnt} / min. ${G.min}` : `${cnt}`;
    const gain = fs.stats.map((st, i) => (P.gs[g][i] || 0) && st.type !== 'production' ? `${P.sn[i] || st.name} ${P.gs[g][i] > 0 ? '+' : ''}${fmt(P.gs[g][i], 2)}` : null).filter(Boolean).join(' · ');
    return `<div class="fgrp${ed.sel?.g === g ? ' on' : ''}"><div class="hd" data-g="${g}" role="button" tabindex="0" title="Choose the smallest size" style="cursor:pointer"><span class="sw" style="background:${grpCol(g, n)}"></span><b>${esc(P.gn[g] || 'Group ' + (g + 1))}</b><span class="ct${low || high ? ' bad' : ''}">${lim}</span></div>
      <div class="sz">${G.items.map((it, s) => { const t = it.tiles, gn = fEffGain(o, ed.fu, ed.cx, g, s); return `<button data-g="${g}" data-s="${s}" class="${ed.sel?.g === g && ed.sel?.s === s ? 'on' : ''}" title="size factor ${fmt(it.multiplierStats, 2)}${gn != null ? ` · efficiency +${gn} %` : ''}">${t[0].length}×${t.length}${gn != null ? ` <span style="color:var(--${gn > 0 ? 'good' : 'fg-3'})">(+${gn} %)</span>` : ''}</button>`; }).join('')}</div>
      ${gain ? `<small>per size unit: ${esc(gain)}</small>` : ''}</div>`;
  }).join('');
  const pick = (g, s) => { ed.mode = 'furn'; ed.sel = { g, s, r: ed.sel?.g === g ? Math.min(ed.sel.r, fs.groups[g].rotations) : 0 }; edModeBtns(); edGroups(); edDraw(); edHint(); };
  fGroups.querySelectorAll('.sz button').forEach(b => b.addEventListener('click', () => pick(+b.dataset.g, +b.dataset.s)));
  const smallest = g => { let best = 0, ba = Infinity; fs.groups[g].items.forEach((it, s) => { const a = it.tiles.flat().filter(x => x != null).length; if (a < ba) { ba = a; best = s; } }); return best; };
  fGroups.querySelectorAll('.hd').forEach(h => { const go = () => pick(+h.dataset.g, smallest(+h.dataset.g)); h.addEventListener('click', go); h.addEventListener('keydown', e => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); go(); } }); });
}
// Pflichtmöbel-Prüfung (seit Version 28): Lassen sich alle Pflichtmöbel (G.min) in diesem Raum überhaupt gemeinsam setzen?
// Durchsucht alle Größen, Drehungen und Lagen im leeren Raum mit den gesetzten Türen (ohne Türen: jede einzelne Tür im Wandring).
// true = es gibt eine Anordnung, false = nein (Raum zu klein), null = zu viele Pflichtteile oder Rechenbudget erschöpft.
// Anlass: Restaurant (canteen_normal) 4 × 3 und 5 × 4 (Kochstelle braucht an beiden Längsseiten eine erreichbare Kachel).
const mandCache = new Map();
function mandFeasible(o, fu) {
  const fs = fu.fs, need = []; fs.groups.forEach((G, g) => { for (let k = 0; k < (G.min || 0); k++) need.push(g); });
  if (!need.length) return true; if (need.length > 3) return null;
  const base = fCtx(o, fu, []), { gridW: gw, gridH: gh, room } = base;
  const key = `${o.t}|${o.cells.slice().sort((x, y) => x - y).join(',')}|${o.d.slice().sort((x, y) => x - y).join(',')}|${o.x},${o.y}`;
  if (mandCache.has(key)) return mandCache.get(key);
  let doorSets = [[...base.doors]];
  if (fs.mustBeIndoors && !base.doors.size) { doorSets = []; for (let r = 0; r < gh; r++) for (let c = 0; c < gw; c++) if (!room[r][c] && [[0, 1], [1, 0], [0, -1], [-1, 0]].some(([dr, dc]) => room[r + dr]?.[c + dc])) doorSets.push([`${r},${c}`]); }
  let budget = 0, res = false; const t0 = performance.now();
  const mk = (pl, doors) => { const cx = PC.createRoomContext(fs, fu.bld, room, pl, gw, gh, doors); cx.ext = base.ext; return cx; };
  const dfs = (i, pl, doors) => {
    if (i === need.length) { const u = PC.findUnreachableMRTiles(mk(pl, doors)); return !u.unreachable.length && !u.disconnected; }
    const g = need[i], G = fs.groups[g], cx = mk(pl, doors);
    for (let s = 0; s < G.items.length; s++) for (let r = 0; r <= G.rotations; r++) for (let y = 0; y < gh; y++) for (let x = 0; x < gw; x++) {
      if (--budget < 0 || ((budget & 4095) === 0 && performance.now() - t0 > 2000)) throw 0;
      if (!PC.canPlaceWithReason(cx, g, s, r, y, x).ok) continue;
      if (dfs(i + 1, [...pl, { groupIdx: g, itemIdx: s, rotation: r, row: y, col: x }], doors)) return true;
    }
    return false;
  };
  try { for (const ds of doorSets) { budget = 400000; if (dfs(0, [], new Set(ds))) { res = true; break; } } } catch { res = null; }
  mandCache.set(key, res); return res;
}
function edStats() {
  const o = edObj(), { fs } = ed.fu, cx = ed.cx, st = fStats(o, ed.fu, cx), warn = [];
  fs.groups.forEach((G, g) => { const c = o.f.filter(p => p[0] === g).length; if (c < (G.min || 0)) warn.push(['bad', `${ed.fu.P.gn[g] || 'Group ' + (g + 1)}: at least ${G.min} needed, ${c} placed`]); if (G.max != null && c > G.max) warn.push(['bad', `${ed.fu.P.gn[g] || 'Group ' + (g + 1)}: at most ${G.max} allowed`]); });
  if (fs.groups.some((G, g) => o.f.filter(p => p[0] === g).length < (G.min || 0)) && mandFeasible(o, ed.fu) === false) {
    const names = [...new Set(fs.groups.map((G, g) => G.min ? (ed.fu.P.gn[g] || 'Group ' + (g + 1)) : null).filter(Boolean))];
    warn.push(['bad', `Room too small: ${names.join(' and ')} ${names.length > 1 ? 'do not fit together' : 'does not fit'} by the room rules (all sizes, rotations and positions${fs.mustBeIndoors && !o.d.length ? ', every door' : ' with these doors'} checked). Enlarge the room.`]);
  }
  if (o.f.length) {
    const u = PC.findUnreachableMRTiles(cx);
    if (u.unreachable.length) warn.push(['bad', `${u.unreachable.length} work or storage tiles cannot be reached`]);
    if (u.disconnected) warn.push(['bad', `${u.disconnected} free tiles are cut off from the rest`]);
  }
  let iso = null, unst = 0;
  if (fs.mustBeIndoors) {
    if (!o.d.length) warn.push(['warn', 'No door. Use “Door” (W) to put one into the wall ring.']);
    iso = PC.isolationInfo(cx);
    if (iso.gaps > iso.free) { const over = iso.gaps - iso.free; warn.push([iso.iso < .85 ? 'bad' : 'warn', `${over} ${over === 1 ? 'door' : 'doors'} above the ${iso.free} free gaps: isolation ${fmtPct(iso.iso)}, upkeep +${Math.round((iso.factor - 1) * 100)} %`]); }
    for (let r = 0; r < cx.gridH; r++) for (let c = 0; c < cx.gridW; c++) if (cx.room[r][c] && PC.tileSupport(cx.room, cx.gridW, cx.gridH, r, c) < PC.STABILITY_THRESHOLD) unst++;
    if (unst) warn.push(['warn', `${unst} tiles too far from a wall. Use “Support” (S) to place ceiling supports.`]);
  }
  ed.unstable = unst;
  if (!warn.length && o.f.length) warn.push(['ok', 'No problems found']);
  const rcs = fRecipes(o, ed.fu, cx), notes = st.filter(x => x.note).map(x => `${x.name}: ${x.note}`);
  const wo = workersOf(o), empRow = st.find(x => x.emp || ['workers', 'men', 'priests', 'guards'].includes(fs.stats[x.i].name));
  fStatsEl.innerHTML = `<h4>Values</h4>${st.length || wo ? `<dl class="fstat">${wo ? `<dt>Workers</dt><dd>${esc(wkTxt(wo))}</dd>` : ''}${st.filter(x => !(wo && x === empRow)).map(x => `<dt>${esc(x.name)}</dt><dd style="${x.cls ? `color:var(--${x.cls})` : ''}">${esc(x.txt)}</dd>`).join('')}${iso != null ? `<dt>Isolation</dt><dd style="color:var(--${iso.iso >= .999 ? 'good' : iso.iso >= .85 ? 'warn' : 'bad'})">${fmtPct(iso.iso)}</dd><dt>Gaps / free</dt><dd>${iso.gaps} / ${iso.free}</dd><dt>Upkeep factor</dt><dd>× ${fmt(iso.factor, 2)}</dd>` : ''}<dt>Furniture</dt><dd>${o.f.length}</dd></dl>` : '<p class="muted">This room has no values from furniture.</p>'}
    ${notes.length || wo?.note ? `<p class="muted">${esc([...notes, wo?.note].filter(Boolean).join(' · '))}</p>` : ''}
    ${rcs.length ? (() => { const cur = Math.min(rcs.length - 1, o.p?.rc ?? 0), bn = BT.get(o.t)?.n || o.t, rcB = BT.get(o.t)?.rc || [], same = [...blds.values()].filter(x => x.t === o.t).length;
      return `<h4>Recipe</h4><div class="rcpick">${rcs.map((t, k) => `<label><input type="radio" name="rcPick" value="${k}"${k === cur ? ' checked' : ''}><span><b>${esc(t)}</b> / day${rcB[k]?.i.length ? `<small> from ${esc(rcB[k].i.map(([r]) => resName(r)).join(' + '))}</small>` : ''}</span></label>`).join('')}</div>
      ${same > 1 ? `<button class="btn sm" id="rcAll">All ${same} × ${esc(bn)} to this recipe</button>` : ''}<p class="muted">The chosen recipe applies to output and balance. The game always shows recipe 1 for the room.</p>`; })() : ''}
    <h4>Notes</h4><ul class="fwarn">${warn.map(([c, t]) => `<li class="${c}">${esc(t)}</li>`).join('') || '<li>Nothing placed yet.</li>'}</ul>
    <p class="muted">As in the game: efficiency = 50 % + 50 % × helper value ÷ workers, at most 100 %. Output = recipe rate × workers × efficiency, without bonuses from technologies.</p>${iso != null ? `<p class="muted">Isolation as in the game: every door is a gap, free are ${iso.free} (one tenth of the ${iso.edge} edge tiles, rounded up). Less isolation multiplies upkeep jobs and upkeep material by 1 + 2 × (1 − isolation).</p>` : ''}`;
  fStatsEl.querySelectorAll('input[name="rcPick"]').forEach(r => r.addEventListener('change', () => setRecipe(o, +r.value, false)));
  document.getElementById('rcAll')?.addEventListener('click', () => setRecipe(o, Math.min(rcs.length - 1, o.p?.rc ?? 0), true));
}
// Rezept für einen Betrieb oder alle Betriebe dieses Typs setzen (gilt für Output und Bilanz)
function setRecipe(o, k, all) {
  const list = all ? [...blds.values()].filter(x => x.t === o.t) : [o];
  commit(); for (const x of list) x.p = { ...(x.p || {}), rc: k };
  dirty(); if (ed) edSync();
  if (all) toast(`${list.length} × ${BT.get(o.t)?.n || o.t} now run with recipe ${k + 1}.`);
}
function edHint() {
  if (!ed) return; const o = edObj();
  ed.gn = null;
  if (ed.mode === 'room') { fHint.textContent = 'Room: dragging a rectangle with the left button adds tiles, with the right button removes them. Furniture that no longer fits drops out.'; return; }
  if (ed.mode === 'door') { fHint.textContent = 'Door: click a tile of the wall ring (not a corner). Click again to remove it.'; return; }
  if (ed.mode === 'pillar') { fHint.textContent = 'Support: click a room tile, the game builds a wall there that carries the roof. Yellow = too far from a wall. Clicking a support removes it.'; return; }
  if (!ed.sel) { fHint.textContent = 'Choose a group or size on the left (E larger, Q smaller, R rotates). Right click removes a furniture piece, clicking the wall ring sets a door.'; return; }
  const G = ed.fu.fs.groups[ed.sel.g], t = fTiles(ed.fu.fs, ed.sel.g, ed.sel.s, ed.sel.r);
  let why = '';
  if (ed.hov) { const p = edPos(); const res = PC.canPlaceWithReason(ed.cx, ed.sel.g, ed.sel.s, ed.sel.r, p.r, p.c); ed.ok = res.ok; why = res.ok ? '' : ' · ' + ({ 'Out of bounds': 'sticks out of the room', 'Not on room tile': 'sticks out of the room', 'Overlaps furniture': 'covers another furniture piece', 'Would block a reachable tile': 'a work or storage tile would be blocked', 'Would block existing furniture': 'blocks an existing furniture piece', 'Furniture would be fully enclosed': 'would be completely enclosed', 'Would split room': 'would cut the room apart' }[res.reason] || res.reason); }
  const gn = fEffGain(o, ed.fu, ed.cx, ed.sel.g, ed.sel.s); ed.gn = gn;
  fHint.textContent = `${ed.fu.P.gn[ed.sel.g] || 'Group'} ${t[0].length} × ${t.length}${gn != null ? ` (efficiency +${gn} %)` : ''}${G.items.length > 1 ? ' · E larger, Q smaller' : ''}${G.rotations ? ' · R rotates' : ''}${why}`;
}
function edPos() { const t = fTiles(ed.fu.fs, ed.sel.g, ed.sel.s, ed.sel.r); return { r: ed.hov.r - ((t.length - 1) >> 1), c: ed.hov.c - ((t[0].length - 1) >> 1) }; }
function edDraw() {
  if (!ed) return; const o = edObj(); if (!o) return;
  const d = window.devicePixelRatio || 1, cw = fcv.width / d, ch = fcv.height / d, cx = ed.cx, gw = cx.gridW, gh = cx.gridH;
  const VM = ED_VM, z = Math.max(4, Math.min(56, Math.floor(Math.min((cw - 24) / (gw + 2 * VM), (ch - 24) / (gh + 2 * VM))))), x0 = Math.floor((cw - gw * z) / 2), y0 = Math.floor((ch - gh * z) / 2);
  ed.z = z; ed.ox = x0; ed.oy = y0;
  const g = fx2; g.setTransform(d, 0, 0, d, 0, 0); g.fillStyle = '#080b0e'; g.fillRect(0, 0, cw, ch);
  const n = ed.fu.fs.groups.length, walled = isWalled(o.t);
  // Umgebung: andere Gebäude, fremde Wandringe, Straßen, Mauern, Kartenrand
  for (let r = -VM; r < gh + VM; r++) for (let c = -VM; c < gw + VM; c++) {
    const X = x0 + c * z, Y = y0 + r * z, x = o.x - 1 + c, y = o.y - 1 + r;
    if (!inMap(x, y)) { g.fillStyle = '#030405'; g.fillRect(X, Y, z, z); continue; }
    const mi = y * W + x, u = occ[mi];
    if (u && u !== o.u) { const ob = blds.get(u); g.fillStyle = ob ? `rgba(${hexRgb(CAT_COL[BT.get(ob.t)?.c] || '#888')},0.28)` : '#2b2f38'; g.fillRect(X, Y, z, z); }
    else if (wcnt[mi] && !o._ring.has(mi)) { g.fillStyle = `rgba(${COL_RING},0.55)`; g.fillRect(X, Y, z, z); }
    else if (ceil[mi]) { g.fillStyle = `rgba(${COL_CEIL},0.55)`; g.fillRect(X, Y, z, z); }
    else if (terr[mi] === 1) { g.fillStyle = 'rgba(160,140,100,0.35)'; g.fillRect(X, Y, z, z); }
    else if (terr[mi] === 2) { g.fillStyle = 'rgba(110,115,122,0.7)'; g.fillRect(X, Y, z, z); }
    else if (!(r >= 0 && c >= 0 && r < gh && c < gw)) { g.fillStyle = (r + c) & 1 ? '#0d1115' : '#0b0f13'; g.fillRect(X, Y, z, z); }
  }
  for (let r = 0; r < gh; r++) for (let c = 0; c < gw; c++) {
    const X = x0 + c * z, Y = y0 + r * z, mi = (o.y - 1 + r) * W + o.x - 1 + c;
    if (cx.room[r][c]) { g.fillStyle = (r + c) & 1 ? '#232c35' : '#202830'; g.fillRect(X, Y, z, z); }
    else if (walled && o._ring.has(mi)) { g.fillStyle = o.d.includes(mi) ? `rgb(${COL_DOOR})` : `rgb(${COL_RING})`; g.fillRect(X, Y, z, z); }
  }
  if (walled) for (const k of edHoles(cx)) { const X = x0 + (k % gw) * z, Y = y0 + ((k / gw) | 0) * z; g.fillStyle = '#9aa0a8'; g.beginPath(); g.arc(X + z / 2, Y + z / 2, z * .3, 0, 7); g.fill(); }
  if (walled && ed.unstable) { g.fillStyle = `rgba(230,190,60,${ed.mode === 'pillar' ? 0.45 : 0.30})`; for (let r = 0; r < gh; r++) for (let c = 0; c < gw; c++) if (cx.room[r][c] && PC.tileSupport(cx.room, gw, gh, r, c) < PC.STABILITY_THRESHOLD) g.fillRect(x0 + c * z, y0 + r * z, z, z); }
  const drawPiece = (p, alpha, bad) => {
    const cells = fCells(ed.fu.fs, p); g.globalAlpha = alpha;
    for (const [x, y, k] of cells) {
      const c = x - o.x + 1, r = y - o.y + 1, X = x0 + c * z, Y = y0 + r * z, tt = ed.fu.fs.tileTypes[k], bl = blocks(ed.fu.fs, k);
      g.fillStyle = bad ? (bl ? '#a8483a' : '#6e3a33') : grpCol(p[0], n, bl ? 42 : 26); g.fillRect(X + 1, Y + 1, z - 2, z - 2);
      if (tt?.mustBeReachable && z >= 10) { g.fillStyle = 'rgba(255,245,220,0.85)'; g.beginPath(); g.arc(X + z / 2, Y + z / 2, Math.max(1.5, z * .12), 0, 7); g.fill(); }
      else if (tt?.kind === 2 && z >= 10) { g.strokeStyle = 'rgba(255,245,220,0.6)'; g.lineWidth = 1; g.strokeRect(X + z * .3, Y + z * .3, z * .4, z * .4); }
    }
    const set = new Set(cells.map(([x, y]) => y * W + x)); g.strokeStyle = bad ? '#ff8a70' : grpCol(p[0], n, 72); g.lineWidth = Math.max(1, z / 14); g.beginPath();
    for (const [x, y] of cells) { const X = x0 + (x - o.x + 1) * z, Y = y0 + (y - o.y + 1) * z; if (!set.has((y - 1) * W + x)) { g.moveTo(X, Y); g.lineTo(X + z, Y); } if (!set.has((y + 1) * W + x)) { g.moveTo(X, Y + z); g.lineTo(X + z, Y + z); } if (!set.has(y * W + x - 1)) { g.moveTo(X, Y); g.lineTo(X, Y + z); } if (!set.has(y * W + x + 1)) { g.moveTo(X + z, Y); g.lineTo(X + z, Y + z); } }
    g.stroke(); g.globalAlpha = 1;
  };
  for (const p of o.f) drawPiece(p, 1, false);
  if (ed.mode === 'furn' && ed.sel && ed.hov) {
    const p = edPos(); drawPiece([ed.sel.g, ed.sel.s, ed.sel.r, o.x - 1 + p.c, o.y - 1 + p.r], .78, ed.ok === false);
    if (ed.gn != null) {
      const t = fTiles(ed.fu.fs, ed.sel.g, ed.sel.s, ed.sel.r), txt = `Efficiency +${ed.gn} %`;
      g.font = '12px Consolas, monospace'; const tw = g.measureText(txt).width + 12;
      let lx = x0 + (p.c + t[0].length) * z + 6, ly = y0 + p.r * z - 22; if (lx + tw > cw - 4) lx = x0 + p.c * z - tw - 6; if (ly < 4) ly = y0 + (p.r + t.length) * z + 6;
      g.fillStyle = 'rgba(12,16,20,0.92)'; g.fillRect(lx, ly, tw, 18); g.strokeStyle = ed.gn > 0 ? GOOD : '#9a8e80'; g.lineWidth = 1; g.strokeRect(lx + .5, ly + .5, tw - 1, 17);
      g.fillStyle = ed.gn > 0 ? GOOD : '#d0c8b8'; g.textAlign = 'left'; g.textBaseline = 'middle'; g.fillText(txt, lx + 6, ly + 9.5);
    }
  } else if (ed.mode !== 'furn' && ed.hov) { g.strokeStyle = GOLD; g.lineWidth = 2; g.strokeRect(x0 + ed.hov.c * z + 1, y0 + ed.hov.r * z + 1, z - 2, z - 2); }
  if (ed.rdrag) { const a = ed.rdrag.a, b = ed.rdrag.b, c0 = Math.min(a.c, b.c), r0 = Math.min(a.r, b.r), c1 = Math.max(a.c, b.c), r1 = Math.max(a.r, b.r); g.fillStyle = ed.rdrag.add ? 'rgba(110,190,120,0.25)' : 'rgba(208,90,72,0.3)'; g.fillRect(x0 + c0 * z, y0 + r0 * z, (c1 - c0 + 1) * z, (r1 - r0 + 1) * z); g.strokeStyle = ed.rdrag.add ? GOOD : BAD; g.lineWidth = 2; g.strokeRect(x0 + c0 * z + 1, y0 + r0 * z + 1, (c1 - c0 + 1) * z - 2, (r1 - r0 + 1) * z - 2); g.fillStyle = '#e8e0d0'; g.font = '12px Consolas, monospace'; g.textAlign = 'left'; g.textBaseline = 'bottom'; g.fillText(`${c1 - c0 + 1} × ${r1 - r0 + 1}`, x0 + c0 * z + 2, y0 + r0 * z - 3); }
  else if (ed.mode === 'room' && ed.hov) { g.strokeStyle = GOLD; g.lineWidth = 2; g.strokeRect(x0 + ed.hov.c * z + 1, y0 + ed.hov.r * z + 1, z - 2, z - 2); }
  g.strokeStyle = 'rgba(180,150,85,0.5)'; g.lineWidth = 1; g.strokeRect(x0 - .5, y0 - .5, gw * z + 1, gh * z + 1);
}
// Raum vergrößern oder verkleinern: Rechteck in lokalen Koordinaten (Innenfläche + 1 Rand) hinzufügen oder abziehen
function edRoomRect(a, b, add) {
  const o = edObj(); if (!o) return;
  const x0 = o.x - 1, y0 = o.y - 1, rect = [];
  for (let r = Math.min(a.r, b.r); r <= Math.max(a.r, b.r); r++) for (let c = Math.min(a.c, b.c); c <= Math.max(a.c, b.c); c++) if (inMap(x0 + c, y0 + r)) rect.push((y0 + r) * W + x0 + c);
  const set = new Set(o.cells); let nc;
  if (add) {
    nc = [...o.cells, ...rect.filter(i => !set.has(i))]; if (nc.length === o.cells.length) return;
    if (!fitsCells(o.t, nc, [o])) { toast('There is no room: another building or its wall ring is in the way.'); return; }
    if (components(nc).length > 1) { toast('The new area must connect to the room.'); return; }
  } else {
    const rs = new Set(rect); nc = o.cells.filter(i => !rs.has(i)); if (nc.length === o.cells.length) return;
    if (!nc.length) { toast('The room needs at least one tile.'); return; }
    if (components(nc).length > 1) { toast('The room would fall apart.'); return; }
  }
  const xs = nc.map(i => i % W), ys = nc.map(i => (i / W) | 0);
  if (Math.max(...xs) - Math.min(...xs) + 1 > 60 || Math.max(...ys) - Math.min(...ys) + 1 > 60) { toast('At most 60 × 60 tiles in the editor.'); return; }
  const before = o.f.length; commit(); reshape(o, nc, o.d); dirty(); edSync();
  if (o.f.length < before) toast(`${before - o.f.length} furniture pieces no longer fitted and were removed.`);
}
function edTile(e) { const r = fcv.getBoundingClientRect(); return { c: Math.floor((e.clientX - r.left - ed.ox) / ed.z), r: Math.floor((e.clientY - r.top - ed.oy) / ed.z) }; }
function edRemoveAt(t) {
  const o = edObj(), pi = ed.cx.occupancy[t.r]?.[t.c]; if (pi == null || pi < 0) return false;
  commit(); o.f = o.f.filter((_, i) => i !== pi); dirty(); edSync(); return true;
}
fcv.addEventListener('contextmenu', e => e.preventDefault());
fcv.addEventListener('pointermove', e => { if (!ed) return; ed.hov = edTile(e); if (ed.rdrag) ed.rdrag.b = ed.hov; edHint(); edDraw(); });
window.addEventListener('pointerup', () => { if (!ed?.rdrag) return; const d = ed.rdrag; ed.rdrag = null; edRoomRect(d.a, d.b, d.add); edDraw(); });
fcv.addEventListener('pointerleave', () => { if (!ed) return; ed.hov = null; edHint(); edDraw(); });
fcv.addEventListener('pointerdown', e => {
  if (!ed || ed.busy) return; const t = edTile(e), o = edObj(), cx = ed.cx;
  if (ed.mode === 'room') { if (e.button === 0 || e.button === 2) { ed.rdrag = { a: t, b: t, add: e.button === 0 }; fcv.setPointerCapture?.(e.pointerId); edDraw(); } return; }
  if (e.button === 2) { edRemoveAt(t); return; }
  if (e.button !== 0) return;
  const mi = (o.y - 1 + t.r) * W + o.x - 1 + t.c;
  if (ed.mode === 'door') { edDoor(t); return; }
  if (ed.mode === 'pillar') { edPillar(t); return; }
  if (isWalled(o.t) && o._ring.has(mi) && !cx.room[t.r]?.[t.c]) { if (edHoles(cx).has(t.r * cx.gridW + t.c)) edPillar(t); else edDoor(t); return; }
  if (!ed.sel) { if (cx.occupancy[t.r]?.[t.c] >= 0) toast('Right click removes the furniture piece.'); return; }
  ed.hov = t; const p = edPos(), res = PC.canPlaceWithReason(cx, ed.sel.g, ed.sel.s, ed.sel.r, p.r, p.c);
  if (!res.ok) { edHint(); toast(fHint.textContent.split(' · ').pop()); return; }
  commit(); o.f = [...o.f, [ed.sel.g, ed.sel.s, ed.sel.r, o.x - 1 + p.c, o.y - 1 + p.r]]; dirty(); edSync();
});
function edKey(e, k) {
  if (ed.busy) return true;
  if (k === 'a') { edAuto(); return true; }
  if (k === 'escape') { if (ed.mode !== 'furn') edSetMode('furn'); else if (ed.sel) { ed.sel = null; edGroups(); edDraw(); edHint(); } else closeFurnish(); return true; }
  if ((k === 'e' || k === 'q') && ed.sel) { const n = ed.fu.fs.groups[ed.sel.g].items.length, ns = Math.max(0, Math.min(n - 1, ed.sel.s + (k === 'e' ? 1 : -1))); if (ns === ed.sel.s) toast(k === 'e' ? 'This is already the largest variant.' : 'This is already the smallest variant.'); ed.sel.s = ns; edGroups(); edDraw(); edHint(); return true; }
  if (k === 'r' && ed.sel) { const G = ed.fu.fs.groups[ed.sel.g]; if (!G.rotations) { toast('In the game this furniture piece has only one orientation.'); return true; } ed.sel.r = (ed.sel.r + 1) % (G.rotations + 1); edDraw(); edHint(); return true; }
  if ((k === 'delete' || k === 'backspace') && ed.hov) { edRemoveAt(ed.hov); return true; }
  if (k === 'd') { edSetMode('furn'); return true; }
  if (k === 'f') { edSetMode('room'); return true; }
  if (k === 'w') { edSetMode('door'); return true; }
  if (k === 's') { edSetMode('pillar'); return true; }
  return ['q', 'e', 'd', 's', 'm', 'w', 't', 'k', 'a', 'x', 'h', 'f', ' '].includes(k);   // Kartenkürzel im Editor sperren
}
// Auto-Einrichten (Optimierer aus Syx-Vis): Raumgröße bleibt, gesetzte Möbel und Türen bleiben.
// Ohne Türen darf er Türen vorschlagen; mit Türen fügt er keine hinzu. Stützen darf er setzen, wenn die Decke sie braucht.
async function edAuto() {
  const o = edObj(); if (!o || ed.busy) return;
  const btn = document.getElementById('furnAuto'), fu = ed.fu, cx0 = fCtx(o, fu);
  ed.busy = true; btn.disabled = true; const t0 = performance.now();
  try {
    const res = await OPT.runOptimizer({
      building: fu.bld, furnitureSet: fu.fs, gridW: cx0.gridW, gridH: cx0.gridH,
      room: cx0.room.map(r => [...r]), placements: cx0.placements.map(p => ({ ...p })), doors: new Set(cx0.doors),
      keepShape: true, maxDoors: o.d.length || 0, ext: cx0.ext || null,
      onProgress: (phase, detail, prog) => { btn.textContent = `Calculating … ${Math.round((prog || 0) * 100)} %`; },
    });
    if (!edObj() || edObj() !== o) return;
    const x0 = o.x - 1, y0 = o.y - 1, cells = [], doors = [];
    for (let r = 0; r < cx0.gridH; r++) for (let c = 0; c < cx0.gridW; c++) if (res.room[r][c]) cells.push((y0 + r) * W + x0 + c);
    for (const k of res.doors) { const [r, c] = k.split(',').map(Number); doors.push((y0 + r) * W + x0 + c); }
    const hadDoors = o.d.length > 0, keepDoors = hadDoors ? o.d : doors;
    if (!cells.length || components(cells).length > 1) { toast('Auto-furnish did not return a valid room.'); return; }
    const before = o.f.length, pillars = o.cells.length - cells.length;
    commit(); o.f = res.placements.map(p => [p.groupIdx, p.itemIdx, p.rotation, x0 + p.col, y0 + p.row]); reshape(o, cells, keepDoors); dirty(); edSync();
    const parts = [`${o.f.length - before} furniture pieces placed`];
    if (pillars > 0) parts.push(`${pillars} ${pillars === 1 ? 'support' : 'supports'}`);
    if (!hadDoors && o.d.length) parts.push(`${o.d.length} ${o.d.length === 1 ? 'door' : 'doors'} suggested`);
    if (fu.fs.groups.some((G, g) => o.f.filter(p => p[0] === g).length < (G.min || 0)) && mandFeasible(o, fu) === false) parts.push('required furniture does not fit: room too small');
    toast(`Auto-furnish: ${parts.join(', ')} (${((performance.now() - t0) / 1000).toFixed(1)} s). Ctrl+Z undoes it.`);
  } catch (err) { console.error(err); toast('Auto-furnish ran into an error. The furnishing stays unchanged.'); }
  finally { ed && (ed.busy = false); btn.disabled = false; btn.textContent = 'Auto-furnish'; }
}
document.getElementById('furnAuto').addEventListener('click', edAuto);
document.getElementById('furnClose').addEventListener('click', closeFurnish);
furnDlg.addEventListener('click', e => { if (e.target === furnDlg) closeFurnish(); });
let clearArm = false;
document.getElementById('furnClear').addEventListener('click', e => {
  const o = edObj(); if (!o?.f.length) return; const b = e.currentTarget;
  if (!clearArm) { clearArm = true; b.textContent = 'Really?'; setTimeout(() => { clearArm = false; b.textContent = 'Remove all'; }, 3000); return; }
  clearArm = false; b.textContent = 'Remove all'; commit(); o.f = []; dirty(); edSync();
});

// ---------- Kosten und Wartung (seit Version 31, Phase 4) ----------
// Daten: XD.C je Raum [Ressourcen, Flächenkosten, Möbelkosten je Gruppe, Upgrade-Masken, Upgrade-Boost, Klima, Verfall] (skripte/xdata_ext.mjs).
// Raum je Ressource r: ⌈(Σ Möbelkosten · Größenfaktor + Flächenkosten · Fläche) · Maske[Upgrade][r] · (1 + Stützzuschlag)⌉ (syx71-formeln §BAUKOSTEN).
// Wartung je Tag: Aufträge = Basis · Faktor · (Fläche/48 + Σ Möbelressourcen/64), Material = Basis · Faktor · Σ Möbelressourcen/64,
// Faktor = (1 + 2 · (1 − Isolation)) / CIVIC_MAINTENANCE (§VERFALL UND WARTUNG).
const COSTS = XD.C || {}, STRUCTC = XD.ST || {}, FLOORC = XD.FL || {};
const K_DEF = { wall: 'WOOD', floor: 'DIRT', walk: 20, mt: 0, spd: 1.2 };
const kOpt = () => ({ ...K_DEF, ...(calc.k || {}) });
const setK = (k, v) => { calc.k = { ...kOpt(), [k]: v }; autosave(); };
const WALL_DE = { WOOD: 'Wood', STONE: 'Stone', GRAND: 'Cut stone (Grand)', MUD: 'Mud' };
const upMax = t => (COSTS[t]?.[3]?.length || 1) - 1;
const roomUp = o => Math.max(0, Math.min(upMax(o.t), o.p?.up || 0));
const civMaint = () => 1 + 0.05 * Math.max(0, Math.min(10, kOpt().mt || 0));
function costOf(o) {
  const cd = COSTS[o.t]; if (!cd) return null;
  const [R, A, IT, UM] = cd, u = roomUp(o), mask = UM?.[u] || [], n = R.length;
  const furn = new Array(n).fill(0); let est = false, nof = false;
  const add = (g, m) => { const c = IT[Math.max(0, Math.min(IT.length - 1, g))]; if (c) for (let i = 0; i < n; i++) furn[i] += (c[i] || 0) * m; };
  if (isFixed(o.t)) { const v = fxOf(o); if (v) { let m = 1; if (o.t === HOME_T) m = v.s + 1; else if (FX_MUL[o.t]?.[v.g]?.[v.s] != null && o.t !== '_waterpump') { m = FX_MUL[o.t][v.g][v.s]; est = true; } add(v.g, m); } }
  else { const fu = furnOf(o.t); if (fu) { const off = Math.max(0, IT.length - fu.fs.groups.length); for (const p of o.f || []) add(p[0] + off, fu.fs.groups[p[0]]?.items[p[1]]?.multiplier ?? 1); if (!o.f?.length && IT.length) nof = true; } else if (IT.length) add(0, 1); }
  let teuer = 0, mul = 1;
  if (isWalled(o.t) && !isFixed(o.t)) { const fu = furnOf(o.t); if (fu?.fs.mustBeIndoors) { const cx = fCtx(o, fu); for (let r = 0; r < cx.gridH; r++) for (let c = 0; c < cx.gridW; c++) if (cx.room[r][c] && PC.tileSupport(cx.room, cx.gridW, cx.gridH, r, c) < PC.STABILITY_THRESHOLD) teuer++; mul = 1 + 2 * Math.min(1, 4 * teuer / o.cells.length); } }
  const res = new Map(); let furnSum = 0;
  for (let i = 0; i < n; i++) { const mk = mask[i] ?? 1; furnSum += furn[i] * mk; const v = Math.ceil((furn[i] + (A[i] || 0) * o.cells.length) * mk * mul - 1e-9); if (v > 0) res.set(R[i], (res.get(R[i]) || 0) + v); }
  return { res, furnSum, mul, teuer, est, nof, u };
}
function maintOf(o, c = costOf(o)) {
  const cd = COSTS[o.t]; if (!cd || !c) return null;
  const base = cd[6] ?? 0.75; if (!base) return { jobs: 0, mat: 0, iso: 1, factor: 0 };
  let iso = 1; const fu = furnOf(o.t);
  if (fu?.fs.mustBeIndoors && isWalled(o.t) && !isFixed(o.t)) iso = PC.isolationInfo(fCtx(o, fu)).iso;
  const factor = (1 + 2 * (1 - iso)) / civMaint();
  return { jobs: base * factor * (o.cells.length / 48 + c.furnSum / 64), mat: base * factor * c.furnSum / 64, iso, factor };
}
const resList = m => [...m].sort((a, b) => b[1] - a[1]).map(([r, v]) => `${fmt(v, 0)} ${esc(resName(r))}`).join(', ') || 'nothing';
let mCache = { gen: -1, m: new Map() };
function maintCached(o) { if (mCache.gen !== gen) mCache = { gen, m: new Map() }; if (!mCache.m.has(o.u)) mCache.m.set(o.u, maintOf(o)); return mCache.m.get(o.u); }
function planCost() {
  const k = kOpt(), rooms = new Map(), all = new Map(), add = (m, r, v) => { if (r && v > 0) m.set(r, (m.get(r) || 0) + v); };
  let jobs = 0, mat = 0, nof = 0, est = 0, mulN = 0;
  for (const o of blds.values()) { const c = costOf(o); if (!c) continue; for (const [r, v] of c.res) { add(rooms, r, v); add(all, r, v); } const m = maintOf(o, c); jobs += m.jobs; mat += m.mat; if (c.nof) nof++; if (c.est) est++; if (c.mul > 1) mulN++; }
  // Wand: Wandring ohne Türen + freie Mauern; Decke: Innenfläche der Räume mit Wand + Türen + freie Decken (seit Version 32, Werte aus dem Spiel)
  let ring = 0, doors = 0, wall = 0, road = 0, cl = 0, roof = 0;
  for (let i = 0; i < W * H; i++) { if (wcnt[i]) { if (dcnt[i]) doors++; else ring++; } else if (terr[i] === 2) wall++; else if (terr[i] === 1 && !occ[i]) road++; if (ceil[i]) cl++; }
  for (const o of blds.values()) if (isWalled(o.t)) roof += o.cells.length;
  const [sr, sa, ca] = STRUCTC[k.wall] || [null, 0, 0], [fr, fa] = FLOORC[k.floor] || [null, 0];
  const wallR = (ring + wall) * sa, roofR = (roof + doors + cl) * (ca || 0), roadR = road * fa;
  add(all, sr, wallR + roofR); add(all, fr, roadR);
  let jan = 0, janMax = 0; for (const o of blds.values()) if (o.t === '_janitor') { const w = workersOf(o); jan += w?.need || 0; janMax += w?.max ?? w?.need ?? 0; }
  const perJ = 576 / (20 + Math.max(0, k.walk));
  return { rooms, all, jobs, mat, nof, est, mulN, ring, doors, wall, road, roof, cl, sr, sa, ca, fr, fa, wallR, roofR, roadR, jan, janMax, perJ };
}
function costHtml() {
  const k = kOpt(), P = planCost();
  let h = `<h3 class="ch">Costs and upkeep</h3><div class="grid3" style="grid-template-columns:1fr 1fr">
    <label for="kWall">Wall and roof material<select id="kWall">${Object.keys(STRUCTC).map(s => `<option value="${s}"${s === k.wall ? ' selected' : ''}>${WALL_DE[s] || s}</option>`).join('')}</select></label>
    <label for="kFloor">Road paving<select id="kFloor">${Object.keys(FLOORC).map(s => `<option value="${s}"${s === k.floor ? ' selected' : ''}>${s}</option>`).join('')}</select></label></div>`;
  h += `<table class="ctab"><tr><th>Resource</th><th class="n">Rooms</th><th class="n">total</th></tr>${[...P.all].sort((a, b) => b[1] - a[1]).map(([r, v]) => `<tr><td>${esc(resName(r))}</td><td class="n">${P.rooms.get(r) ? fmt(P.rooms.get(r), 0) : ''}</td><td class="n">${fmt(Math.ceil(v - 1e-9), 0)}</td></tr>`).join('') || '<tr><td colspan="3" class="muted">Nothing in the plan yet.</td></tr>'}</table>`;
  h += `<p class="muted">Walls ${P.ring + P.wall} tiles (wall ring without doors ${P.ring}, free walls ${P.wall}) · ceilings ${P.roof + P.doors + P.cl} tiles (over rooms ${P.roof}, doors ${P.doors}, free ceilings ${P.cl}) · roads ${P.road} tiles. ${P.sa ? `${WALL_DE[k.wall]}: wall ${P.sa}, ceiling ${P.ca} ${esc(resName(P.sr))} per tile.` : 'Mud costs nothing.'}${P.fa ? ` Paving: ${P.fa} ${esc(resName(P.fr))} per tile.` : ''}</p>`;
  if (P.nof) h += `<p class="stale">${P.nof} ${P.nof === 1 ? 'room is' : 'rooms are'} not furnished; their furniture costs are missing.</p>`;
  if (P.mulN) h += `<p class="muted">${P.mulN} ${P.mulN === 1 ? 'room has' : 'rooms have'} tiles far away from a wall and therefore cost more (support surcharge up to × 3). Placing supports lowers the costs.</p>`;
  if (P.est) h += `<p class="muted">For ${P.est} fixed rooms (export, guard post, depot …) the size factor of the costs is estimated.</p>`;
  const cap = P.janMax * P.perJ, need = P.jobs;
  h += `<table class="ctab"><tr><th>Upkeep per day</th><th class="n">Value</th></tr><tr><td>Jobs</td><td class="n">${fmt(need, 1)}</td></tr><tr><td>Material (units)</td><td class="n">${fmt(P.mat, 1)}</td></tr>
    <tr><td>Janitor workers (needed · at most)</td><td class="n">${fmt(P.jan, 0)} · ${fmt(P.janMax, 0)}</td></tr><tr><td>Capacity (≈ ${fmt(P.perJ, 1)} jobs per janitor)</td><td class="n" style="color:var(--${cap >= need ? 'good' : 'bad'})">${fmt(cap, 1)}</td></tr></table>
    <div class="grid3" style="grid-template-columns:1fr 1fr"><label for="kWalk">Walking time per job (s)<input type="number" id="kWalk" min="0" max="600" step="5" value="${k.walk}"></label><label for="kMt">Tech “Maintenance” (MAIN0, 0–10)<input type="number" id="kMt" min="0" max="10" step="1" value="${k.mt}"></label></div>
    <p class="muted">Construction costs as in the game: furniture × size + area, upgrade mask, support surcharge, plus wall and ceiling per tile. The surcharge for the foundation depends on the position on the map and is missing. Upkeep: isolation from the doors, janitor capacity estimated (20 s work plus walking time per job, 576 s working time per day). Demolition and build time are not included.</p>`;
  return h;
}
function costBind(rer) {
  const on = (id, ev, f) => document.getElementById(id)?.addEventListener(ev, f);
  on('kWall', 'change', e => { setK('wall', e.target.value); rer(); });
  on('kFloor', 'change', e => { setK('floor', e.target.value); rer(); });
  on('kWalk', 'change', e => { setK('walk', Math.max(0, +e.target.value || 0)); rer(); });
  on('kMt', 'change', e => { setK('mt', Math.max(0, Math.min(10, Math.round(+e.target.value || 0)))); mCache.gen = -1; needOv = true; schedule(); rer(); });
}
function upSelHtml(o) {
  const n = upMax(o.t); if (n < 1) return '';
  const u = roomUp(o), ub = COSTS[o.t][4];
  return `<label class="muted" for="upSel">Upgrade level</label><select id="upSel">${Array.from({ length: n + 1 }, (_, i) => `<option value="${i}"${i === u ? ' selected' : ''}>${i ? `Level ${i}` : 'none'}${isProd(o.t) && ub?.[i] ? ` (output +${fmt(ub[i] * 100, 0)} %)` : ''}${o.t === '_waterpump' && i ? ` (workers × ${i === 1 ? '2/3' : '1/3'})` : ''}</option>`).join('')}</select>`;
}

// ---------- Boni im Ausstoß (seit Version 31, Phase 6) ----------
// ROOM_X = (1 + Upgrade + Werkzeug + Tech + Adelsamt + Religion ADD) · Rasse MUL · Klima MUL · Religion MUL (§BOOST-KERN, §BONI-QUELLEN).
const BO_DEF = { tech: {}, tools: false, race: '', rel: '', relP: 100, noble: {}, clim: '' };
const boOpt = () => ({ ...BO_DEF, ...(calc.bo || {}) });
const setBo = (k, v) => { calc.bo = { ...boOpt(), [k]: v }; nobleCache.gen = -1; dirty(); };
const boostName = t => ('ROOM_' + t.toUpperCase()).replace(/__/g, '_');
const keyHit = (name, K, kind) => { const full = K ? 'ROOM_' + K : 'ROOM'; return kind === '**' || kind === '*+' ? name.startsWith(full) : name === full; };
function toolAm(t) { const TA = XD.TA; if (!TA || TA.no.includes(t)) return 0; for (const [p, am] of Object.entries(TA.am)) if (t.startsWith(p)) return am; return 0; }
function boRaceShares() {
  const bo = boOpt(); if (!bo.race) return null;
  if (bo.race === 'calc') { const sh = raceShares(); return sh ? sh.map(({ r, f }) => ({ id: r.id, f })) : null; }
  return [{ id: bo.race, f: 1 }];
}
let nobleCache = { gen: -1, emp: {} };
function nobleEmp(rx) {
  if (nobleCache.gen !== gen) nobleCache = { gen, emp: {} };
  if (nobleCache.emp[rx] == null) { const re = new RegExp(rx); let n = 0; for (const o of blds.values()) if (re.test(o.t)) { const pr = isProd(o.t) ? prodOf(o, true) : null; n += pr ? pr.wk : 0; } nobleCache.emp[rx] = n; }
  return nobleCache.emp[rx];
}
function techTotals(t, ri) {
  const bo = boOpt(); let add = 0, tool = 0, cons = 0;
  for (const [tr, id, LV, tgt, val] of XD.T || []) { const L = Math.min(LV, Math.max(0, bo.tech[tr + '/' + id] || 0)); if (!L) continue; const [kind, rid, i] = tgt.split(':'); if (rid !== t) continue; if (kind === 'room') add += L * val; else if (kind === 'tool') tool += L; else if (kind === 'cons' && +i === ri) cons += L * val; }
  return { add, tool, cons };
}
function roomX(o, ri = 0, noNoble = false) {
  const t = o.t, bo = boOpt(), name = boostName(t), parts = []; let add = 0, mul = 1;
  const up = roomUp(o), ub = COSTS[t]?.[4]; if (up && ub?.[up] && isProd(t)) { add += ub[up]; parts.push(`Upgrade +${fmt(ub[up], 2)}`); }
  const tt = techTotals(t, ri);
  if (tt.add) { add += tt.add; parts.push(`Tech +${fmt(tt.add, 2)}`); }
  if (bo.tools) { const am = toolAm(t); if (am && tt.tool) { const b = 2 * Math.min(am, tt.tool) / 8; add += b; parts.push(`Tool +${fmt(b, 2)}`); } }
  if (!noNoble) for (const [k, n, rx] of XD.NO || []) { const rank = bo.noble[k] || 0; if (!rank || !new RegExp(rx).test(t)) continue; const emp = nobleEmp(rx); const b = 2.5 * Math.max(0, Math.min(1, emp > 0 ? (1 + 4 * rank) * 50 / emp : 1)); if (b) { add += b; parts.push(`Noble office +${fmt(b, 2)}`); } }
  if (bo.rel && XD.REL?.[bo.rel]) { const s = Math.max(0, Math.min(100, bo.relP ?? 100)) / 100; let ra = 0, rm = 1; for (const [K, kind, v] of XD.REL[bo.rel][1]) if (keyHit(name, K, kind)) { if (kind.endsWith('+')) ra += v; else rm *= v; } if (ra) { add += ra * s; parts.push(`Religion +${fmt(ra * s, 2)}`); } if (rm !== 1) { const m = 1 + (rm - 1) * s; mul *= m; parts.push(`Religion × ${fmt(m, 2)}`); } }
  const sh = boRaceShares(); if (sh) { let m = 0; for (const { id, f } of sh) { let r = 1; for (const [K, kind, v] of XD.RB?.[id] || []) if (!kind.endsWith('+') && keyHit(name, K, kind)) r *= v; m += f * r; } if (Math.abs(m - 1) > 1e-9) { mul *= m; parts.push(`Race × ${fmt(m, 2)}`); } }
  const cb = COSTS[t]?.[5]; if (bo.clim && cb?.[bo.clim] != null && cb[bo.clim] !== 1) { mul *= cb[bo.clim]; parts.push(`Climate × ${fmt(cb[bo.clim], 2)}`); }
  return { x: (1 + add) * mul, add, mul, parts, cons: 1 + tt.cons };
}
const CLIM_DE = { '': 'not considered', c: 'cold', t: 'temperate', h: 'hot' };
function boHtml() {
  const bo = boOpt(), techN = Object.values(bo.tech).filter(v => v > 0).length;
  const rOpts = [['', 'not considered'], ['calc', 'as in the demand calculator'], ...RACES.map(r => [r.id, r.n])];
  return `<div class="grid3" style="grid-template-columns:1fr 1fr">
    <label for="boClim">Climate<select id="boClim">${Object.entries(CLIM_DE).map(([k, n]) => `<option value="${k}"${k === bo.clim ? ' selected' : ''}>${n}</option>`).join('')}</select></label>
    <label for="boRace">Race of the workers<select id="boRace">${rOpts.map(([k, n]) => `<option value="${k}"${k === bo.race ? ' selected' : ''}>${esc(n)}</option>`).join('')}</select></label>
    <label for="boRel">Religion<select id="boRel"><option value="">none</option>${Object.entries(XD.REL || {}).map(([k, [n]]) => `<option value="${k}"${k === bo.rel ? ' selected' : ''}>${n}</option>`).join('')}</select></label>
    <label for="boRelP">Share of believers %<input type="number" id="boRelP" min="0" max="100" step="5" value="${bo.relP}"></label></div>
    <div class="chkline"><input type="checkbox" id="boTools"${bo.tools ? ' checked' : ''}><label for="boTools">Tools available (as many as the tech allows)</label></div>
    <div class="row"><button class="btn sm" id="boTech">Technologies …</button><span class="muted">${techN ? `${techN} techs set` : 'no techs set'}</span></div>
    <h3>Noble offices “Master of …” (rank)</h3><div class="grid3" style="grid-template-columns:repeat(4,1fr)">${(XD.NO || []).map(([k, n]) => `<label for="boN-${k}">${NOBLE_EN[k] || n}<input type="number" id="boN-${k}" min="0" max="10" step="1" value="${bo.noble[k] || 0}"></label>`).join('')}</div>
    <p class="muted">Bonuses affect output and consumption of workplaces (selection and balance). Race and religion apply proportionally to the workers, climate according to the room file. Without settings the planner calculates as before, without bonuses.</p>`;
}
function boBind() {
  const on = (id, ev, f) => document.getElementById(id)?.addEventListener(ev, f);
  on('boClim', 'change', e => setBo('clim', e.target.value));
  on('boRace', 'change', e => setBo('race', e.target.value));
  on('boRel', 'change', e => setBo('rel', e.target.value));
  on('boRelP', 'change', e => setBo('relP', Math.max(0, Math.min(100, +e.target.value || 0))));
  on('boTools', 'change', e => setBo('tools', e.target.checked));
  on('boTech', 'click', openTech);
  for (const [k] of XD.NO || []) on('boN-' + k, 'change', e => setBo('noble', { ...boOpt().noble, [k]: Math.max(0, Math.min(10, Math.round(+e.target.value || 0))) }));
}
function refreshBo() { const el = document.getElementById('boBody'); if (!el) return; el.innerHTML = boHtml(); boBind(); }
const techDlg = document.getElementById('techDlg'), techBody = document.getElementById('techBody');
function techLabel(tgt, val) { const [kind, rid, i] = tgt.split(':'), n = BT.get(rid)?.n || rid; return kind === 'room' ? `${n}: output +${fmt(val * 100, 0)} % per level` : kind === 'tool' ? `${n}: +1 tool per worker per level` : `${n}, recipe ${+i + 1}: consumption ÷ (1 + 0.1 per level)`; }
// Noble office names come German from skripte/xdata_ext.mjs; shown in English (keys k are unchanged).
const NOBLE_EN = { mine: 'Mines', wood: 'Woodcutters', farm: 'Farms', orchard: 'Orchards', pasture: 'Pastures', fish: 'Fisheries', refiner: 'Refiners', workshop: 'Workshops' };
// Tech tree names stay German in the data because saved settings use them as keys (tree/id); shown in English.
const TREE_EN = { Landwirtschaft: 'Agriculture', Tierhaltung: 'Husbandry', Gewinnung: 'Extraction', Veredelung: 'Refining', Handwerk: 'Crafting' };
function openTech() {
  const bo = boOpt(), trees = new Map();
  for (const e of XD.T || []) { if (!trees.has(e[0])) trees.set(e[0], []); trees.get(e[0]).push(e); }
  techBody.innerHTML = `<div class="row"><button class="btn sm" id="techMax">All to maximum</button><button class="btn sm" id="techZero">All to 0</button><span class="muted">Levels as in the game’s technology tree. Only techs that change output, tools or consumption of workplaces.</span></div>` +
    [...trees].map(([tr, L]) => `<details${[...L].some(e => bo.tech[e[0] + '/' + e[1]] > 0) ? ' open' : ''}><summary>${esc(TREE_EN[tr] || tr)} <span class="muted">(${L.length})</span></summary><div class="techgrid">${L.map(([t0, id, LV, tgt, val]) => `<label><span><b>${id}</b> ${esc(techLabel(tgt, val))}</span><input type="number" data-id="${esc(t0 + '/' + id)}" aria-label="${esc(id + ' ' + techLabel(tgt, val))}" min="0" max="${LV}" step="1" value="${Math.min(LV, bo.tech[t0 + '/' + id] || 0)}"><small>/ ${LV}</small></label>`).join('')}</div></details>`).join('') +
    `<div class="row"><button class="btn primary" id="techClose">Done</button></div>`;
  techDlg.hidden = false;
  const save = () => { const t = {}; techBody.querySelectorAll('input[data-id]').forEach(i => { const v = Math.max(0, Math.min(+i.max, Math.round(+i.value || 0))); if (v) t[i.dataset.id] = v; }); setBo('tech', t); };
  techBody.querySelectorAll('input[data-id]').forEach(i => i.addEventListener('change', save));
  document.getElementById('techMax').addEventListener('click', () => { techBody.querySelectorAll('input[data-id]').forEach(i => { i.value = i.max; }); save(); });
  document.getElementById('techZero').addEventListener('click', () => { techBody.querySelectorAll('input[data-id]').forEach(i => { i.value = 0; }); save(); });
  document.getElementById('techClose').addEventListener('click', () => { techDlg.hidden = true; refreshBo(); });
}
techDlg.addEventListener('click', e => { if (e.target === techDlg) { techDlg.hidden = true; refreshBo(); } });

// ---------- Roundness (seit Version 31, Phase 6; settlement/environment/SettEnvShape, §UMGEBUNG) ----------
// Wand = Wandring ohne Tür oder freie Mauer. Wandrichtung je freier Kachel: diagonal (Innenecke) oder gerade.
// ROUND-Basis: Treppenwand aus ≥ 2 Stufen, SQUARE-Basis: gerade Wand ≥ 5. Ausbreitung bis Abstand 10, ROUND zuerst.
let shapeCache = { gen: -1 };
function computeShape() {
  if (shapeCache.gen === gen) return shapeCache;
  const N = W * H, wallAt = (x, y) => inMap(x, y) && ((wcnt[y * W + x] && !dcnt[y * W + x]) || terr[y * W + x] === 2);
  const free = i => !((wcnt[i] && !dcnt[i]) || terr[i] === 2) && !occ[i];
  const dir = new Int8Array(N);
  for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
    const i = y * W + x; if (!free(i)) continue;
    const n = wallAt(x, y - 1), e = wallAt(x + 1, y), s = wallAt(x, y + 1), w = wallAt(x - 1, y);
    dir[i] = n && e && wallAt(x + 1, y - 1) ? 5 : e && s && wallAt(x + 1, y + 1) ? 6 : s && w && wallAt(x - 1, y + 1) ? 7 : w && n && wallAt(x - 1, y - 1) ? 8 : n ? 1 : e ? 2 : s ? 3 : w ? 4 : 0;
  }
  const at = (x, y) => inMap(x, y) ? dir[y * W + x] : -1;
  const PERP = { 5: [[1, 1], [-1, -1]], 6: [[1, -1], [-1, 1]], 7: [[1, 1], [-1, -1]], 8: [[1, -1], [-1, 1]] };
  const round = [], square = [];
  for (let y = 0; y < H; y++) for (let x = 0; x < W; x++) {
    const d = dir[y * W + x]; if (!d) continue;
    if (d >= 5) { if (PERP[d].some(([dx, dy]) => at(x + dx, y + dy) === d)) round.push(y * W + x); }
    else { const hz = d === 1 || d === 3; if ([-2, -1, 1, 2].every(k => (hz ? at(x + k, y) : at(x, y + k)) === d)) square.push(y * W + x); }
  }
  // Ausbreitung: Kosten 10 gerade, 14 diagonal (Zehntel-Kacheln), bis 100 = Abstand 10; Ergebnis in ganzen Kacheln (255 = nicht erreicht)
  const flood = (src, block) => {
    const t10 = new Uint8Array(N).fill(255), B = Array.from({ length: 101 }, () => []);
    for (const i of src) { t10[i] = 0; B[0].push(i); }
    for (let b = 0; b <= 100; b++) for (let k = 0; k < B[b].length; k++) {
      const i = B[b][k]; if (t10[i] !== b) continue;
      const x = i % W, y = (i / W) | 0;
      for (const [dx, dy] of D8) { const nx = x + dx, ny = y + dy; if (!inMap(nx, ny)) continue; const j = ny * W + nx; if (!free(j) || (block && block[j] !== 255)) continue; const nb = b + (dx && dy ? 14 : 10); if (nb <= 100 && nb < t10[j]) { t10[j] = nb; B[nb].push(j); } }
    }
    const out = new Uint8Array(N).fill(255); for (let i = 0; i < N; i++) if (t10[i] !== 255) out[i] = Math.ceil(t10[i] / 10); return out;
  };
  const rd = flood(round, null), sd = flood(square, rd);
  let rn = 0, sn = 0, tot = 0; for (let i = 0; i < N; i++) { if (terr[i] !== 1 || occ[i] || wcnt[i]) continue; tot++; if (rd[i] !== 255) rn++; else if (sd[i] !== 255) sn++; }
  shapeCache = { gen, rd, sd, round: round.length, square: square.length, rn, sn, tot };
  return shapeCache;
}

// ---------- Analysen: Pendelwege und Lagerwege (seit Version 31, Phase 5; §PRODUKTION) ----------
// Pendeln = cl(1 − (Gehsekunden − 34)/576, 0, 10); Holweg = cl(1 − (Hin- und Rückweg in s − 61)/576, 0, 1). Gehgeschwindigkeit einstellbar (Annahme 1,2 Kacheln/s).
let anaCache = { gen: -1 };
function analysis() {
  const spd = Math.max(0.1, kOpt().spd || 1.2);
  if (anaCache.gen === gen && anaCache.spd === spd) return anaCache;
  const homes = [...blds.values()].filter(o => HOME.has(o.t)), piles = [...blds.values()].filter(o => o.t === '_stockpile');
  const dh = homes.length ? bfs(homes.flatMap(accessTiles), 3000) : null, ds = piles.length ? bfs(piles.flatMap(accessTiles), 3000) : null;
  const near = (d, o) => { if (!d) return null; let m = 65535; for (const i of accessTiles(o)) if (d[i] < m) m = d[i]; return m === 65535 ? null : m; };
  const com = [], sto = [];
  for (const o of blds.values()) {
    if (HOME.has(o.t)) continue;
    const w = workersOf(o); if (w && (w.need || w.max)) { const t = near(dh, o), s = t == null ? null : t / spd; com.push({ o, t, s, f: s == null ? 0 : Math.max(0, Math.min(10, 1 - (s - 34) / 576)) }); }
    const pr = isProd(o.t) ? prodOf(o) : null; if (pr && (pr.out.length || pr.inp.length)) { const t = near(ds, o), s = t == null ? null : 2 * t / spd; sto.push({ o, t, s, f: s == null ? 0 : Math.max(0, Math.min(1, 1 - Math.max(0, s - 61) / 576)) }); }
  }
  anaCache = { gen, spd, com, sto, homes: homes.length, piles: piles.length };
  return anaCache;
}
function anaHtml() {
  const k = kOpt();
  let h = `<div class="row"><label class="muted" for="kSpd">Walking speed</label><input type="number" id="kSpd" min="0.1" max="10" step="0.1" value="${k.spd}"><span class="muted">tiles/s (assumption, check in the game)</span></div>
    <div class="row"><button class="btn sm" id="anaChain">Production chain</button><button class="btn sm" data-ov="commute">Commute</button><button class="btn sm" data-ov="stock">Storage paths</button><button class="btn sm" data-ov="shape">Roundness</button></div>`;
  if (ovMode === 'commute' || ovMode === 'stock') {
    const A = analysis(), L = (ovMode === 'commute' ? A.com : A.sto).slice().sort((a, b) => a.f - b.f);
    const src = ovMode === 'commute' ? A.homes : A.piles;
    if (!src) h += `<p class="stale">No ${ovMode === 'commute' ? 'houses' : 'warehouses'} in the plan.</p>`;
    const avg = L.length ? L.reduce((s, x) => s + x.f, 0) / L.length : 0;
    h += `<p class="muted">${L.length} ${ovMode === 'commute' ? 'workplaces' : 'workplaces'}, Ø factor ${fmtPct(Math.min(1, avg))}. ${ovMode === 'commute' ? 'Walking distance from the nearest house; free up to 34 s, then 576 s down to 0.' : 'There and back to the nearest warehouse; 61 s free, then 576 s down to 0.'}</p>`;
    h += `<table class="ctab"><tr><th>Building</th><th class="n">Tiles</th><th class="n">s</th><th class="n">Factor</th></tr>${L.slice(0, 12).map(x => `<tr data-u="${x.o.u}" style="cursor:pointer"><td>${esc(BT.get(x.o.t)?.n || x.o.t)}</td><td class="n">${x.t ?? '–'}</td><td class="n">${x.s == null ? '–' : fmt(x.s, 0)}</td><td class="n" style="color:var(--${x.f >= .999 ? 'good' : x.f >= .75 ? 'warn' : 'bad'})">${x.s == null ? 'no path' : fmtPct(Math.min(1, x.f))}</td></tr>`).join('')}</table>`;
  } else if (ovMode === 'shape') {
    const S = computeShape();
    h += `<p class="muted">Roads: ${S.rn} of ${S.tot} tiles round, ${S.sn} square (${S.round} round, ${S.square} square source tiles). Green = round (stepped wall, corners bevelled with ceilings or walls), red = square (straight wall from 5 tiles). Effect per race: Cretonians, Garthimi, Tilapi like round, Dondorians square.</p>`;
  }
  return h;
}
function refreshAna() {
  const el = document.getElementById('anaBody'); if (!el) return;
  el.innerHTML = anaHtml();
  document.getElementById('kSpd')?.addEventListener('change', e => { setK('spd', Math.max(0.1, Math.min(10, +e.target.value || 1.2))); anaCache.gen = -1; needOv = true; schedule(); refreshAna(); });
  document.getElementById('anaChain')?.addEventListener('click', openChain);
  el.querySelectorAll('[data-ov]').forEach(b => b.addEventListener('click', () => setOv(ovMode === b.dataset.ov ? 'cov' : b.dataset.ov)));
  el.querySelectorAll('tr[data-u]').forEach(r => r.addEventListener('click', () => { const o = blds.get(+r.dataset.u); if (!o) return; msel = null; selU = o.u; computeSelReach(); refreshPanels(); z = Math.max(z, 8); ox = vw / 2 - (o.x + o.w / 2) * z; oy = vh / 2 - (o.y + o.h / 2) * z; schedule(); }));
}

// ---------- Produktionskette (seit Version 31, Phase 5) ----------
const chainDlg = document.getElementById('chainDlg'), chainBody = document.getElementById('chainBody');
function chainData() {
  const types = new Map(), bal = new Map();
  for (const o of blds.values()) {
    const pr = prodOf(o); if (!pr) continue;
    const T = types.get(o.t) || { t: o.t, n: 0, wk: 0, out: new Map(), inp: new Map() }; T.n++; T.wk += pr.wk;
    for (const [r, a] of pr.out) { T.out.set(r, (T.out.get(r) || 0) + a); bal.set(r, (bal.get(r) || 0) + a); }
    for (const [r, a] of pr.inp) { T.inp.set(r, (T.inp.get(r) || 0) + a); bal.set(r, (bal.get(r) || 0) - a); }
    types.set(o.t, T);
  }
  const prodBy = new Map(); for (const T of types.values()) for (const r of T.out.keys()) { if (!prodBy.has(r)) prodBy.set(r, []); prodBy.get(r).push(T); }
  const depth = new Map(), dep = (T, seen = new Set()) => { if (depth.has(T.t)) return depth.get(T.t); if (seen.has(T.t)) return 0; seen.add(T.t); let d = 0; for (const r of T.inp.keys()) for (const P of prodBy.get(r) || []) d = Math.max(d, dep(P, seen) + 1); depth.set(T.t, d); return d; };
  for (const T of types.values()) dep(T);
  const missing = new Map(); for (const T of types.values()) for (const [r, a] of T.inp) if (!prodBy.has(r)) missing.set(r, (missing.get(r) || 0) + a);
  return { types, bal, prodBy, depth, missing };
}
function openChain() {
  const D = chainData(), cols = new Map();
  for (const T of D.types.values()) { const d = D.depth.get(T.t) + (D.missing.size ? 1 : 0); if (!cols.has(d)) cols.set(d, []); cols.get(d).push(T); }
  if (D.missing.size) cols.set(0, [...D.missing].map(([r, a]) => ({ miss: r, a })));
  if (!D.types.size) { chainBody.innerHTML = '<p class="muted">No workplaces in the plan yet.</p><div class="row"><button class="btn primary" id="chainClose">Close</button></div>'; chainDlg.hidden = false; document.getElementById('chainClose').addEventListener('click', () => { chainDlg.hidden = true; }); return; }
  const NW = 170, NH = 44, GX = 90, GY = 16, keys = [...cols.keys()].sort((a, b) => a - b), pos = new Map();
  let maxRows = 0; keys.forEach((k, ci) => { const L = cols.get(k); maxRows = Math.max(maxRows, L.length); L.forEach((T, ri) => pos.set(T.miss ? 'miss:' + T.miss : T.t, { x: 10 + ci * (NW + GX), y: 10 + ri * (NH + GY) })); });
  const Wd = 20 + keys.length * (NW + GX) - GX, Hd = 20 + maxRows * (NH + GY) - GY;
  let edges = '', nodes = '';
  for (const T of D.types.values()) {
    const ins = []; for (const [r, a] of T.inp) { const P = D.prodBy.get(r) || []; for (const s of (P.length ? P.map(p => p.t) : ['miss:' + r])) ins.push([r, a, s]); }
    ins.forEach(([r, a, s], k) => { const A = pos.get(s), B = pos.get(T.t); if (!A || !B) return; const bad = (D.bal.get(r) || 0) < -1e-6, off = (k - (ins.length - 1) / 2) * Math.min(12, (NH - 8) / Math.max(1, ins.length - 1)); const x1 = A.x + NW, y1 = A.y + NH / 2, x2 = B.x, y2 = B.y + NH / 2 + off, mx = (x1 + x2) / 2;
      edges += `<path d="M${x1},${y1} C${mx},${y1} ${mx},${y2} ${x2},${y2}" fill="none" stroke="${bad ? BAD : 'rgba(180,150,85,0.55)'}" stroke-width="${bad ? 2 : 1.4}"/><text x="${x2 - 6}" y="${y2 + (off < 0 ? -3 : off > 0 ? 10 : -4)}" text-anchor="end" font-size="10.5" fill="${bad ? BAD : '#b0a898'}">${esc(resName(r))} ${fmt(a, 1)}</text>`; });
  }
  for (const [k, p] of pos) {
    if (k.startsWith('miss:')) { const r = k.slice(5); nodes += `<g><rect x="${p.x}" y="${p.y}" width="${NW}" height="${NH}" rx="4" fill="rgba(208,90,72,0.18)" stroke="${BAD}"/><text x="${p.x + 8}" y="${p.y + 18}" font-size="12" fill="#f2ece0">${esc(resName(r))}</text><text x="${p.x + 8}" y="${p.y + 34}" font-size="10.5" fill="${BAD}">missing: ${fmt(D.missing.get(r), 1)} / day</text></g>`; continue; }
    const T = D.types.get(k), b = BT.get(k), col = CAT_COL[b?.c] || '#888', outs = [...T.out].map(([r, a]) => `${fmt(a, 1)} ${resName(r)}`).join(', ');
    const short = [...T.out.keys()].some(r => (D.bal.get(r) || 0) < -1e-6);
    nodes += `<g><rect x="${p.x}" y="${p.y}" width="${NW}" height="${NH}" rx="4" fill="rgba(20,26,32,0.95)" stroke="${short ? BAD : col}" stroke-width="${short ? 2 : 1.2}"/><text x="${p.x + 8}" y="${p.y + 17}" font-size="12" fill="#f2ece0">${esc((b?.n || k).slice(0, 20))} × ${T.n}</text><text x="${p.x + 8}" y="${p.y + 33}" font-size="10.5" fill="#9a8e80">${esc((`${fmt(T.wk, 0)} wk. · ${outs}`).slice(0, 30))}</text></g>`;
  }
  const deficits = [...D.bal].filter(([, v]) => v < -1e-6).sort((a, b) => a[1] - b[1]);
  chainBody.innerHTML = `<p class="muted">Flow of goods between the workplaces in the plan, per day. Columns by chain level, raw materials on the left. Red: more consumption than production (bottleneck) or a raw material without a producer in the plan. Demand of the residents is in the balance.</p>
    <div class="chainwrap"><svg viewBox="0 0 ${Wd} ${Hd}" width="${Wd}" height="${Hd}" font-family="Segoe UI, system-ui, sans-serif">${edges}${nodes}</svg></div>
    ${deficits.length ? `<p class="stale">Bottlenecks: ${deficits.map(([r, v]) => `${esc(resName(r))} ${fmt(v, 1)}`).join(', ')} per day.</p>` : '<p class="muted" style="color:var(--good)">No bottlenecks between the workplaces.</p>'}
    <div class="row"><button class="btn primary" id="chainClose">Close</button></div>`;
  chainDlg.hidden = false; document.getElementById('chainClose').addEventListener('click', () => { chainDlg.hidden = true; });
}
chainDlg.addEventListener('click', e => { if (e.target === chainDlg) chainDlg.hidden = true; });

// ---------- Einrichtung auf gleiche Räume übertragen (seit Version 31, Phase 7) ----------
// Gleicher Typ und gleiche Form, auch gedreht. Möbel und Türen werden mitgedreht; was im Ziel nicht passt, fällt weg.
function relShape(o) { return o.cells.map(c => [c % W - o.x, ((c / W) | 0) - o.y]); }
const shapeKey = (L) => L.map(([x, y]) => x + ',' + y).sort().join(' ');
function rotRel(L, h) { return L.map(([x, y]) => [h - 1 - y, x]); }
function copyFurnish(src) {
  const base = relShape(src), sF = fRel(src, src.x, src.y), sD = doorXY(src).map(([x, y]) => [x - src.x, y - src.y]);
  const variants = []; let L = base, F = sF, Dd = sD, w = src.w, h = src.h;
  for (let k = 0; k < 4; k++) { variants.push({ key: shapeKey(L), F, D: Dd, w, h }); F = fRot(src.t, F, h); Dd = Dd.map(([x, y]) => [h - 1 - y, x]); L = rotRel(L, h); [w, h] = [h, w]; }
  let n = 0, lost = 0; const targets = [...blds.values()].filter(o => o !== src && o.t === src.t);
  if (!targets.length) { toast('There is no other room of this type.'); return; }
  commit();
  for (const o of targets) {
    const v = variants.find(q => q.w === o.w && q.h === o.h && q.key === shapeKey(relShape(o))); if (!v) continue;
    const doors = isWalled(o.t) ? v.D.map(([x, y]) => (o.y + y) * W + o.x + x).filter(i => validDoor(o, i) && doorsFree([i], [o])) : o.d;
    if (isWalled(o.t)) reshape(o, o.cells, doors);
    o.f = fAbs(v.F, o.x, o.y); const before = o.f.length; fKeep(o); lost += before - o.f.length;
    if (src.p?.rc != null) o.p = { ...(o.p || {}), rc: src.p.rc };
    n++;
  }
  if (!n) { undoS.pop(); redoS.length = 0; toast('No other room of this type has the same shape (not even rotated).'); return; }
  dirty(); toast(`Furnishing copied to ${n} ${n === 1 ? 'room' : 'rooms'}${lost ? `, ${lost} furniture pieces did not fit` : ''}. Ctrl+Z undoes it.`);
}

// ---------- Vorschaubilder der Vorlagen (seit Version 31, Phase 7) ----------
function tplThumb(T) {
  const c = document.createElement('canvas'), s = Math.max(1, Math.floor(44 / Math.max(T.w, T.h)) || 1);
  c.width = Math.max(1, T.w * s); c.height = Math.max(1, T.h * s); c.className = 'thumb'; c.setAttribute('aria-hidden', 'true');
  const g = c.getContext('2d'); g.fillStyle = 'rgb(26,33,40)'; g.fillRect(0, 0, c.width, c.height);
  for (const [v, x, y, w, h] of T.ter) { g.fillStyle = v === 1 ? `rgb(${COL_ROAD})` : `rgb(${COL_WALL})`; g.fillRect(x * s, y * s, w * s, h * s); }
  for (const [x, y, w, h] of T.cl || []) { g.fillStyle = `rgb(${COL_CEIL})`; g.fillRect(x * s, y * s, w * s, h * s); }
  for (const e of T.b) { const [t, x, y, w, h] = e, col = CAT_COL[BT.get(t)?.c] || '#888'; if (isWalled(t)) { g.fillStyle = `rgb(${COL_RING})`; g.fillRect((x - 1) * s, (y - 1) * s, (w + 2) * s, (h + 2) * s); } g.fillStyle = col; g.globalAlpha = 0.85; g.fillRect(x * s, y * s, w * s, h * s); g.globalAlpha = 1; }
  return c;
}

// ---------- Plan-Varianten vergleichen (seit Version 31, Phase 7) ----------
const cmpDlg = document.getElementById('cmpDlg'), cmpBody = document.getElementById('cmpBody');
function planMetrics() {
  const homes = [...blds.values()].filter(o => o.t === '_home'), pop = homes.reduce((s, o) => s + residentsOf(o), 0), P = planCost(), Pr = computeProd();
  const top = [...P.all].sort((a, b) => b[1] - a[1]).slice(0, 4).map(([r, v]) => `${fmt(Math.ceil(v), 0)} ${resName(r)}`).join(', ');
  return { W, H, b: blds.size, homes: homes.length, pop, jobs: Pr.jobs, jobsMax: Pr.jobsMax, cost: [...P.all.values()].reduce((s, v) => s + v, 0), top, maint: P.jobs, cap: P.janMax * P.perJ, deficit: [...Pr.per].filter(([, e]) => e.p - e.c < -1e-6).length };
}
function openCompare() {
  const plans = plansList(); const s = snap(), keepCalc = calc, keepName = planName, rows = [{ n: `${isSampleName(planName) ? 'Current plan' : planName} (current)`, m: planMetrics() }];
  try { for (const p of plans) { try { calc = keepCalc; fromObj({ ...p, calc: p.calc || keepCalc }); calc = { ...keepCalc, ...(p.calc || {}), k: keepCalc.k, bo: keepCalc.bo }; gen++; rows.push({ n: p.name, m: planMetrics() }); } catch { rows.push({ n: p.name, m: null }); } } }
  finally { calc = keepCalc; planName = keepName; restore(s); document.getElementById('planName').value = isSampleName(keepName) ? '' : keepName; }
  const cols = [['Map', m => `${m.W} × ${m.H}`], ['Buildings', m => m.b], ['Houses', m => m.homes], ['Residents', m => fmt(m.pop, 0)], ['Workers needed', m => `${fmt(m.jobs, 0)} (max ${fmt(m.jobsMax, 0)})`], ['Construction costs total', m => fmt(m.cost, 0)], ['mostly', m => esc(m.top)], ['Upkeep / day', m => `${fmt(m.maint, 1)} of ${fmt(m.cap, 1)}`], ['Goods with bottleneck', m => m.deficit]];
  cmpBody.innerHTML = `<p class="muted">Saved plans from this browser compared with the current one. Costs with the chosen wall material and road paving, bonuses as currently set.</p>${plans.length ? '' : '<p class="stale">No saved plans yet. Enter a name under “Save &amp; share” and save.</p>'}
    <div class="chainwrap"><table class="ctab"><tr><th>Value</th>${rows.map(r => `<th class="n">${esc(r.n)}</th>`).join('')}</tr>${cols.map(([n, f]) => `<tr><td>${n}</td>${rows.map(r => `<td class="n">${r.m ? f(r.m) : 'unreadable'}</td>`).join('')}</tr>`).join('')}</table></div>
    <div class="row"><button class="btn primary" id="cmpClose">Close</button></div>`;
  cmpDlg.hidden = false; document.getElementById('cmpClose').addEventListener('click', () => { cmpDlg.hidden = true; });
}
cmpDlg.addEventListener('click', e => { if (e.target === cmpDlg) cmpDlg.hidden = true; });
document.getElementById('cmpBtn').addEventListener('click', openCompare);

// ---------- Kartenansichten der Phasen 4–6 ----------
const OV2 = ['iso', 'maint', 'shape', 'commute', 'stock'];
function paintOv2() {
  const im = ovX.createImageData(W, H), d = im.data, see = anyLayer();
  const put = (i, c, a) => { const k = i * 4; d[k] = c[0]; d[k + 1] = c[1]; d[k + 2] = c[2]; d[k + 3] = see ? a * .55 : a; };
  const grade = f => f >= .999 ? RG_GOOD : f >= .75 ? RG_WARN : RG_BAD;
  if (ovMode === 'iso') { for (const o of blds.values()) { if (!(furnOf(o.t)?.fs.mustBeIndoors && isWalled(o.t) && !isFixed(o.t))) continue; const m = maintCached(o); if (!m) continue; for (const c of o.cells) put(c, grade(m.iso), 130); } }
  else if (ovMode === 'maint') { let mx = 0; const L = []; for (const o of blds.values()) { const m = maintCached(o); if (!m) continue; const v = m.jobs / o.cells.length; L.push([o, v]); if (v > mx) mx = v; } for (const [o, v] of L) { const f = mx ? v / mx : 0; for (const c of o.cells) put(c, f < .34 ? RG_GOOD : f < .67 ? RG_WARN : RG_BAD, 60 + Math.round(f * 110)); } }
  else if (ovMode === 'commute' || ovMode === 'stock') { const A = analysis(); for (const x of ovMode === 'commute' ? A.com : A.sto) for (const c of x.o.cells) put(c, x.s == null ? RG_BAD : grade(Math.min(1, x.f)), 140); }
  else if (ovMode === 'shape') { const S = computeShape(); for (let i = 0; i < W * H; i++) { if (S.rd[i] !== 255) put(i, RG_GOOD, 160 - S.rd[i] * 10); else if (S.sd[i] !== 255) put(i, RG_BAD, 160 - S.sd[i] * 10); } }
  ovX.putImageData(im, 0, 0);
}
const OV2_NOTE = {
  iso: 'Isolation of the indoor rooms from the doors: green 100 %, yellow from 75 %, red below. Less isolation means more upkeep.',
  maint: 'Upkeep jobs per tile and day, compared between rooms: green little, red much.',
  shape: 'Roundness on free tiles: green round, red square, paler with distance. List under “Analyses”.',
  commute: 'Commute from the nearest house: green without loss, yellow from 75 %, red below or no path. List under “Analyses”.',
  stock: 'Path to the nearest warehouse (there and back): green without loss, yellow from 75 %, red below or no warehouse. List under “Analyses”.',
};

// ---------- sample ----------
function isSampleName(n) { return /^(Beispiel|Example)/.test(n || ''); }
function sample() {
  W = 120; H = 60; allocGrids(); blds = new Map(); nextU = 1; radOv = {};
  const O = 4;   // zwei Blöcke 37 × 37 teilen sich die Randstraße
  tplPut(tplById('wohnblock-aus'), O, O); tplPut(tplById('gewerbeblock-bare'), O + 36, O);
  planName = 'Example: residential and commercial block 37';
}

// ---------- boot ----------
let booted = false;
try { const c = lsGet(LS_CUR); if (c) { fromObj(JSON.parse(c)); booted = true; } } catch { booted = false; }
if (!booted) sample();
new ResizeObserver(() => { const first = !vw; resize(); if (first) fit(); }).observe(stage);
syncSizeInputs(); setTool('sel'); setOv('cov'); refreshPalette(); refreshPlans(); refreshTpls(); sRim.disabled = sv().k === 1; footUpd(); refreshBo(); refreshAna(); dirty();
for (const im of imgs.values()) im.addEventListener('load', schedule, { once: true });
idbOpen().then(async db => { idb = db; const recs = await idbAll(); layers = recs.filter(r => r.blob).map(makeLayer); actLayer = layers[0]?.id || null; refreshLayers(); needBase = true; schedule(); });
})();
