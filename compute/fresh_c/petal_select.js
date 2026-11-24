// Exact solver for the 7-request game on 2k points with one fixed edge (port of exact7.py to Node for speed).
// Same model, same reductions (see exact7.py header and FRESH_C.md section 12): states are multisets of
// membership types of the points of D_j, canonicalised under permutations of the edge labels; plain AND/OR
// search with a transposition table; the last request is evaluated by the exact closed form (validated against
// enumeration in exact7.py).  No relaxation.
'use strict';

const PERMS = {};
function permutations(arr) {
  if (arr.length <= 1) return [arr.slice()];
  const out = [];
  for (let i = 0; i < arr.length; i++) {
    const rest = arr.slice(0, i).concat(arr.slice(i + 1));
    for (const p of permutations(rest)) out.push([arr[i]].concat(p));
  }
  return out;
}
for (let i = 1; i <= 5; i++) {
  const maps = [];
  for (const p of permutations([...Array(i).keys()])) {
    const mp = new Int32Array(1 << i);
    for (let m = 0; m < (1 << i); m++) {
      let v = 0;
      for (let b = 0; b < i; b++) if ((m >> b) & 1) v |= 1 << p[b];
      mp[m] = v;
    }
    maps.push(mp);
  }
  PERMS[i] = maps;
}

// canonical form under edge relabelling.  Edges are first ordered by an invariant signature; only edges with
// equal signatures are permuted exhaustively, so the result is a true canonical form at a fraction of the cost.
const PERMCACHE = new Map();
function groupPerms(groups) {            // groups: array of arrays of positions (sorted order) -> list of orderings
  const key = groups.map(g => g.length).join('.');
  let res = PERMCACHE.get(key);
  if (res) return res;
  let acc = [[]];
  let offset = 0;
  for (const g of groups) {
    const idx = [...Array(g.length).keys()].map(x => x + offset);
    const ps = permutations(idx);
    const next = [];
    for (const a of acc) for (const p of ps) next.push(a.concat(p));
    acc = next;
    offset += g.length;
  }
  PERMCACHE.set(key, acc);
  return acc;
}
function canon(masks, counts, n, i) {
  // signatures
  const sig = new Array(i);
  for (let b = 0; b < i; b++) {
    let size = 0;
    const parts = [];
    for (let j = 0; j < n; j++) if ((masks[j] >> b) & 1) { size += counts[j]; parts.push(popc(masks[j]) * 64 + counts[j]); }
    parts.sort((x, y) => x - y);
    const inter = [];
    for (let c = 0; c < i; c++) if (c !== b) {
      let t = 0;
      for (let j = 0; j < n; j++) if (((masks[j] >> b) & 1) && ((masks[j] >> c) & 1)) t += counts[j];
      inter.push(t);
    }
    inter.sort((x, y) => x - y);
    sig[b] = size + '|' + parts.join(',') + '|' + inter.join(',');
  }
  const order = [...Array(i).keys()].sort((x, y) => (sig[x] < sig[y] ? -1 : sig[x] > sig[y] ? 1 : 0));
  const groups = [];
  for (let p = 0; p < i; p++) {
    if (p > 0 && sig[order[p]] === sig[order[p - 1]]) groups[groups.length - 1].push(p);
    else groups.push([p]);
  }
  const orders = groupPerms(groups);     // each: array pos -> index into `order`
  let best = null;
  const tmp = new Array(n);
  const newpos = new Array(i);
  for (const ord of orders) {
    // edge order[ord[p]] gets new label p
    for (let p = 0; p < i; p++) newpos[order[ord[p]]] = p;
    for (let j = 0; j < n; j++) {
      let m = masks[j], v = 0;
      for (let b = 0; b < i; b++) if ((m >> b) & 1) v |= 1 << newpos[b];
      tmp[j] = v * 64 + counts[j];
    }
    tmp.sort((a, b) => a - b);
    if (best === null) { best = tmp.slice(); continue; }
    let less = false;
    for (let j = 0; j < n; j++) {
      if (tmp[j] < best[j]) { less = true; break; }
      if (tmp[j] > best[j]) break;
    }
    if (less) best = tmp.slice();
  }
  return best;
}

function vectors(caps, total) {
  const n = caps.length;
  const suffix = new Array(n + 1).fill(0);
  for (let j = n - 1; j >= 0; j--) suffix[j] = suffix[j + 1] + caps[j];
  const out = [];
  const cur = new Array(n).fill(0);
  (function rec(j, rem) {
    if (j === n) { if (rem === 0) out.push(cur.slice()); return; }
    const lo = Math.max(0, rem - suffix[j + 1]);
    const hi = Math.min(caps[j], rem);
    for (let v = hi; v >= lo; v--) { cur[j] = v; rec(j + 1, rem - v); }
    cur[j] = 0;
  })(0, total);
  return out;
}

function popc(x) { let c = 0; while (x) { x &= x - 1; c++; } return c; }

class Game {
  constructor(k, T) {
    this.k = k; this.T = T;
    this.memo = new Map();
    this.best = new Map();
    this.deadline = Infinity;
    this.timedOut = false;
    this.usePairBound = true;
    this.pruned = 0;
  }
  // state: array of codes (canonical).  returns array of {tot, key(string), code(array)|null, a}
  children(state, i, s) {
    const k = this.k;
    const n = state.length;
    const masks = new Array(n), cnt = new Array(n), rest = new Array(n);
    let U = 0;
    for (let j = 0; j < n; j++) { masks[j] = state[j] >> 6; cnt[j] = state[j] & 63; rest[j] = cnt[j] - s[j]; U += rest[j]; }
    const b = 1 << i, full = (1 << (i + 1)) - 1;
    const replies = (U <= k) ? [rest] : vectors(rest, k);
    const seen = new Set();
    const res = [];
    const im = [], ic = [];
    for (const a of replies) {
      im.length = 0; ic.length = 0;
      for (let j = 0; j < n; j++) {
        if (a[j]) { im.push(masks[j] | b); ic.push(a[j]); }
        if (cnt[j] - a[j]) { im.push(masks[j]); ic.push(cnt[j] - a[j]); }
      }
      // relevance filter
      const rm = [], rc = [];
      let tot = 0;
      for (let x = 0; x < im.length; x++) {
        const need = full & ~im[x];
        let ok = false;
        for (let y = 0; y < im.length; y++) if ((im[y] & need) === need) { ok = true; break; }
        if (ok) { rm.push(im[x]); rc.push(ic[x]); tot += ic[x]; }
      }
      if (i + 1 <= 5) {
        const code = canon(rm, rc, rm.length, i + 1);
        const key = code.join(',');
        if (seen.has(key)) continue;
        seen.add(key);
        res.push({ tot, key, code, a });
      } else {
        if (seen.has(tot)) continue;
        seen.add(tot);
        res.push({ tot, key: null, code: null, a });
      }
    }
    res.sort((x, y) => y.tot - x.tot);
    return res;
  }
  lastRound(state) {
    const k = this.k, T = this.T, n = state.length;
    const masks = state.map(c => c >> 6), cnt = state.map(c => c & 63);
    const adj = new Array(n).fill(0);
    for (let a = 0; a < n; a++) {
      const need = 31 & ~masks[a];
      for (let b = 0; b < n; b++) if ((masks[b] & need) === need) adj[a] |= 1 << b;
    }
    const all = (1 << n) - 1;
    let found = null, bail = false;
    const evalB = (B, cost) => {
      const theta = all & ~B;
      if (popc(theta) > k) { bail = true; return; }
      let nb = 0;
      for (let j = 0; j < n; j++) if ((theta >> j) & 1) nb |= adj[j];
      let dn = 0, uOut = 0;
      const outT = theta & ~nb;
      for (let j = 0; j < n; j++) { if ((nb >> j) & 1) dn += cnt[j]; if ((outT >> j) & 1) uOut += cnt[j]; }
      const tIn = popc(theta & nb), nOut = popc(outT);
      const uLeft = Math.max(nOut, uOut - (T - cost));
      const d6 = dn + Math.min(k - tIn, uLeft);
      if (d6 <= T) found = B;
    };
    const rec = (j, B, cost) => {
      if (found !== null || bail) return;
      if (j === n) { evalB(B, cost); return; }
      if (cost + cnt[j] <= T) rec(j + 1, B | (1 << j), cost + cnt[j]);
      rec(j + 1, B, cost);
    };
    rec(0, 0, 0);
    if (bail && found === null) return null;
    if (found !== null) return { block: masks.filter((m, j) => (found >> j) & 1) };
    return false;
  }
  win(state, i) {
    const T = this.T;
    let tot = 0;
    for (const c of state) tot += c & 63;
    if (tot <= T) return true;
    if (i === 6) return false;
    const key = i + ':' + state.join(',');
    const m = this.memo.get(key);
    if (m !== undefined) return m;
    if (this.timedOut) return false;
    if (Date.now() > this.deadline) { this.timedOut = true; return false; }
    if (i === 5) {
      const r = this.lastRound(state);
      if (r !== null) {
        const w = r !== false;
        this.memo.set(key, w);
        if (w) this.best.set(key, r);
        return w;
      }
    }
    const n = state.length;
    const masks = state.map(c => c >> 6), cnt = state.map(c => c & 63);
    const full = (1 << i) - 1;
    if (this.usePairBound && this.pairBound(masks, cnt, n, full, tot, 6 - i)) { this.memo.set(key, false); this.pruned++; return false; }
    const w = new Array(n).fill(0);
    for (let a = 0; a < n; a++) {
      const need = full & ~masks[a];
      for (let b = 0; b < n; b++) if ((masks[b] & need) === need) w[a] += cnt[b];
    }
    const reqs = vectors(cnt, T);
    const score = s => { let x = 0; for (let j = 0; j < n; j++) x += s[j] * w[j]; return x; };
    reqs.sort((a, b) => score(b) - score(a));
    // adversary replies are generated lazily, heaviest types first, and tested as they come
    const ordT = [...Array(n).keys()].sort((x, y) => w[y] - w[x]);
    const b = 1 << i, full1 = (1 << (i + 1)) - 1, k = this.k;
    const self = this;
    let result = false;
    const rest = new Array(n), a = new Array(n).fill(0);
    const im = [], ic = [], rm = [], rc = [];
    for (const s of reqs) {
      let U = 0;
      for (let j = 0; j < n; j++) { rest[j] = cnt[j] - s[j]; U += rest[j]; }
      const seen = new Set();
      let ok = true;
      const test = () => {            // returns false if this reply refutes the request
        im.length = 0; ic.length = 0;
        for (let j = 0; j < n; j++) {
          if (a[j]) { im.push(masks[j] | b); ic.push(a[j]); }
          if (cnt[j] - a[j]) { im.push(masks[j]); ic.push(cnt[j] - a[j]); }
        }
        rm.length = 0; rc.length = 0;
        let tot2 = 0;
        for (let x = 0; x < im.length; x++) {
          const need = full1 & ~im[x];
          let hit = false;
          for (let y = 0; y < im.length; y++) if ((im[y] & need) === need) { hit = true; break; }
          if (hit) { rm.push(im[x]); rc.push(ic[x]); tot2 += ic[x]; }
        }
        if (tot2 <= T) return true;
        if (i + 1 === 6) return false;
        const code = canon(rm, rc, rm.length, i + 1);
        const ck = code.join(',');
        if (seen.has(ck)) return true;
        seen.add(ck);
        return self.win(code, i + 1);
      };
      if (U <= k) {
        for (let j = 0; j < n; j++) a[j] = rest[j];
        ok = test();
      } else {
        const suffix = new Array(n + 1).fill(0);
        for (let p = n - 1; p >= 0; p--) suffix[p] = suffix[p + 1] + rest[ordT[p]];
        const rec = (p, rem) => {
          if (!ok) return;
          if (p === n) { if (rem === 0 && !test()) ok = false; return; }
          const j = ordT[p];
          const lo = Math.max(0, rem - suffix[p + 1]);
          const hi = Math.min(rest[j], rem);
          for (let v = hi; v >= lo && ok; v--) { a[j] = v; rec(p + 1, rem - v); }
          a[j] = 0;
        };
        rec(0, k);
      }
      if (this.timedOut) return false;
      if (ok) { result = true; this.best.set(key, { req: s.slice() }); break; }
    }
    this.memo.set(key, result);
    return result;
  }
  // Sound certificate that the adversary wins: every reply kills only pairs lying inside D \ A, a set of
  // q = max(T, |D| - k) points, and at the end the surviving pairs must live on at most T points.  With
  // kap(q) >= max number of alive pairs (loops included) inside any q points:  P > rho*kap(q) + kap(T)  =>  loss.
  pairBound(masks, cnt, n, full, tot, rho) {
    const k = this.k, T = this.T;
    const deg = new Array(n).fill(0);
    let P2 = 0;
    for (let a = 0; a < n; a++) {
      const need = full & ~masks[a];
      let d = 0;
      for (let b = 0; b < n; b++) if ((masks[b] & need) === need) d += cnt[b];
      if (masks[a] === full) d += 1;            // own type is adjacent: others of the type (cnt-1) + loop counted twice
      deg[a] = d;
      P2 += d * cnt[a];
    }
    const order = [...Array(n).keys()].sort((x, y) => deg[y] - deg[x]);
    const kap = q => {
      let rem = q, sum = 0;
      for (const j of order) { const t = Math.min(rem, cnt[j]); sum += t * deg[j]; rem -= t; if (!rem) break; }
      return Math.min(sum / 2, q * (q - 1) / 2 + q);
    };
    const q = Math.max(T, tot - k);
    return P2 / 2 > rho * kap(q) + kap(T) + 1e-9;
  }
  root() {
    const k = this.k;
    return canon([1, 0], [k, k], 2, 1);
  }
}

function fmtMask(m) { let s = ''; for (let b = 0; b < 6; b++) if ((m >> b) & 1) s += (b + 1); return s || '-'; }
function fmtState(state) { return '{' + state.map(c => fmtMask(c >> 6) + ':' + (c & 63)).join(', ') + '}'; }

function mainLine(g) {
  const lines = [];
  let state = g.root(), i = 1;
  for (;;) {
    let tot = 0; for (const c of state) tot += c & 63;
    if (tot <= g.T) { lines.push(`  after ${i} edges: |D| = ${tot} <= T, types ${fmtState(state)} -> request D, win`); break; }
    const mv = g.best.get(i + ':' + state.join(','));
    if (!mv) { lines.push(`  after ${i} edges: |D| = ${tot} types ${fmtState(state)} (no stored move)`); break; }
    if (mv.block) {
      lines.push(`  after ${i} edges: |D| = ${tot} types ${fmtState(state)}  FINAL request: all of types [${mv.block.map(fmtMask).join(', ')}] + spare budget on addable points -> |D_6| <= T`);
      break;
    }
    const s = mv.req;
    const reqStr = state.map((c, j) => s[j] ? fmtMask(c >> 6) + ':' + s[j] : null).filter(x => x).join(', ');
    lines.push(`  after ${i} edges: |D| = ${tot} types ${fmtState(state)}  request {${reqStr}}`);
    const ch = g.children(state, i, s).filter(c => c.tot > g.T);
    if (ch.length === 0) { lines.push(`  every reply leaves |D| <= T`); break; }
    state = ch[0].code; i += 1;
  }
  return lines;
}


// ---- four-petal confined game (TWIN 15): four fixed replies, three further requests -----------------------
// A configuration is a list of (type mask over the 4 petals, count).  Requester wins iff engine.win(state, 4).
const quadCache = new Map();
let quadCalls = 0, quadTime = 0;
function quadWin(g, masks, counts) {          // masks over 4 petals; only points in covering pairs matter
  const rm = [], rc = [];
  for (let x = 0; x < masks.length; x++) {
    if (!counts[x]) continue;
    const need = 15 & ~masks[x];
    let ok = false;
    for (let y = 0; y < masks.length; y++) if (counts[y] && (masks[y] & need) === need) { ok = true; break; }
    if (ok) { rm.push(masks[x]); rc.push(counts[x]); }
  }
  if (rm.length === 0) return true;
  const code = canon(rm, rc, rm.length, 4);
  const key = code.join(',');
  let r = quadCache.get(key);
  if (r !== undefined) return r;
  const t0 = Date.now();
  r = g.win(code, 4);
  quadCalls++; quadTime += Date.now() - t0;
  quadCache.set(key, r);
  return r;
}
function Lstar(a, b) {
  const c = [a + b / 3, b + a / 3, 2 * (a + b) / 3];
  if (b >= a / 2) c.push(3 * a / 4 + b / 2);
  if (a >= b / 2) c.push(3 * b / 4 + a / 2);
  return Math.min(...c);
}

// ---- C4: selection game in the open setting.  J replies; she wins iff some four of them are triple-free and
// form a requester-winning four-petal configuration (exact table, evaluated on demand).  m = J + 3 requests.
// usage: node petal_select.js k T Jmax [seconds]
const k = parseInt(process.argv[2]), T = parseInt(process.argv[3]), Jmax = parseInt(process.argv[4]);
const limit = process.argv[5] ? parseFloat(process.argv[5]) : 1100;
const g = new Game(k, T);
const FULL = !!process.env.FULL;      // FULL: any four replies, exact four-petal value (triple points allowed)
function winningQuad(masks, cnt, n, j) {
  for (let a = 0; a < j; a++) for (let b = a + 1; b < j; b++) for (let c = b + 1; c < j; c++) for (let d = c + 1; d < j; d++) {
    const pm = new Map();
    let bad = false;
    for (let x = 0; x < n && !bad; x++) {
      const m = masks[x];
      const v = ((m >> a) & 1) | (((m >> b) & 1) << 1) | (((m >> c) & 1) << 2) | (((m >> d) & 1) << 3);
      const pc = popc(v);
      if (pc === 4 || (pc >= 3 && !FULL)) bad = true;      // a common point of the four petals is never allowed
      else if (pc >= 1) pm.set(v, (pm.get(v) || 0) + cnt[x]);        // singles matter as partners of triple points
    }
    if (bad) continue;
    const mm = [...pm.keys()], cc = mm.map(v => pm.get(v));
    if (quadWin(g, mm, cc)) return [a + 1, b + 1, c + 1, d + 1];
  }
  return null;
}
const memoAS = new Map();
let deadline = 0, timedOut = false;
function asWin(state, j, J) {
  const n = state.length;
  const masks = state.map(c => c >> 6), cnt = state.map(c => c & 63);
  if (j >= 4 && winningQuad(masks, cnt, n, j)) return true;
  if (j === J) return false;
  const key = J + '|' + j + ':' + state.join(',');
  const mm = memoAS.get(key);
  if (mm !== undefined) return mm;
  if (timedOut) return false;
  if (Date.now() > deadline) { timedOut = true; return false; }
  let total = 0; for (const c of cnt) total += c;
  const reqs = vectors(cnt, Math.min(T, total));
  const score = s => { let x = 0; for (let y = 0; y < n; y++) x += s[y] * popc(masks[y]); return -x; };
  reqs.sort((a, b) => score(a) - score(b));     // points of high degree first (keeps the replies triple-free)
  const b = 1 << j;
  let result = false;
  const a = new Array(n).fill(0), rest = new Array(n);
  for (const s of reqs) {
    for (let x = 0; x < n; x++) rest[x] = cnt[x] - s[x];
    let ok = true;
    const seen = new Set();
    const rec = (x, used) => {
      if (!ok) return;
      if (x === n) {
        const im = [], ic = [];
        for (let y = 0; y < n; y++) { if (a[y]) { im.push(masks[y] | b); ic.push(a[y]); } if (cnt[y] - a[y]) { im.push(masks[y]); ic.push(cnt[y] - a[y]); } }
        if (k - used) { im.push(b); ic.push(k - used); }
        const code = canon(im, ic, im.length, j + 1);
        const ck = code.join(',');
        if (seen.has(ck)) return;
        seen.add(ck);
        if (!asWin(code, j + 1, J)) ok = false;
        return;
      }
      for (let v = Math.min(rest[x], k - used); v >= 0 && ok; v--) { a[x] = v; rec(x + 1, used + v); }
      a[x] = 0;
    };
    rec(0, 0);
    if (timedOut) return false;
    if (ok) { result = true; break; }
  }
  memoAS.set(key, result);
  return result;
}
console.log(`C4  k=${k} T=${T} (T/k=${(T / k).toFixed(4)}): selection of four petals with a requester-winning configuration; ${FULL ? 'ANY four replies (exact four-petal value)' : 'triple-free quadruples only'}`);
for (let J = 4; J <= Jmax; J++) {
  const t0 = Date.now();
  deadline = t0 + limit * 1000; timedOut = false;
  const r = asWin([1 * 64 + k], 1, J);
  console.log(`  J=${J} replies (m = ${J + 3} requests): ${timedOut ? 'UNDECIDED (time limit)' : (r ? 'REQUESTER can always obtain four winning petals' : 'ADVERSARY can keep every four replies losing')}   states=${memoAS.size}, four-petal configurations evaluated ${quadCache.size} (R: ${[...quadCache.values()].filter(x => x).length}) [${((Date.now() - t0) / 1000).toFixed(1)}s]`);
  if (r && !timedOut) break;
}
