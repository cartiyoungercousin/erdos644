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

// ---- C1, C2, C3 tables.   usage: node petal.js k T
const k = parseInt(process.argv[2]), T = parseInt(process.argv[3]);
const g = new Game(k, T);
const P = { 12: 3, 13: 5, 14: 9, 23: 6, 24: 10, 34: 12 };
console.log(`k=${k} T=${T} (T/k=${(T / k).toFixed(4)})`);
// C1(b): two pairs with cores a (petals 1,2) and b (petals 3,4); cross cells all 0 or all 1
for (const cross of [0, 1]) {
  const mism = [];
  let rows = 0, agree = 0;
  const grid = [];
  for (let a = 0; a + 2 * cross <= k; a++) {
    let line = '';
    for (let b = 0; b + 2 * cross <= k; b++) {
      const r = quadWin(g, [P[12], P[34], P[13], P[14], P[23], P[24]], [a, b, cross, cross, cross, cross]);
      const pred = Math.ceil(Lstar(a, b) - 1e-9) <= T;
      rows++; if (r === pred) agree++; else mism.push(`(a=${a},b=${b}: exact ${r ? 'R' : 'A'}, L*=${Lstar(a, b).toFixed(2)})`);
      line += r ? 'R' : 'A';
    }
    grid.push(`a=${String(a).padStart(2)}: ${line}`);
  }
  console.log(`C1(b) two pairs, cross cells = ${cross}: ${rows} configurations, prediction "R iff ceil(L*(a,b)) <= T" agrees on ${agree}`);
  console.log('   rows a = 0.., columns b = 0..   ' + grid.join(' | '));
  console.log('   disagreements: ' + (mism.join(' ') || 'none'));
}
// C1(c): triple-free configurations with pair cells from a grid of values
{
  const step = k <= 9 ? 1 : (k <= 12 ? 2 : 3);
  let n = 0, nR = 0, suffR = 0, suffTot = 0; const viol = []; const seen = new Set();
  const vals = []; for (let v = 0; v <= k; v += step) vals.push(v);
  for (const c12 of vals) for (const c34 of vals) for (const c13 of vals) for (const c24 of vals) for (const c14 of vals) for (const c23 of vals) {
    if (c12 + c13 + c14 > k || c12 + c23 + c24 > k || c13 + c23 + c34 > k || c14 + c24 + c34 > k) continue;
    const key = [[c12, c34].sort(), [c13, c24].sort(), [c14, c23].sort()].map(x => x.join('.')).sort().join('|');
    if (seen.has(key)) continue; seen.add(key);
    const r = quadWin(g, [P[12], P[34], P[13], P[24], P[14], P[23]], [c12, c34, c13, c24, c14, c23]);
    n++; if (r) nR++;
    const suff = (c12 + c34 <= T) && (c13 + c24 <= T) && (c14 + c23 <= T);
    if (suff) { suffTot++; if (r) suffR++; else viol.push(`(${c12},${c34};${c13},${c24};${c14},${c23})`); }
  }
  console.log(`C1(c) triple-free configurations on the grid step ${step}: ${n} configurations, requester wins ${nR}; of the ${suffTot} with all three loads c12+c34, c13+c24, c14+c23 <= T she wins ${suffR}` + (viol.length ? '; exceptions: ' + viol.slice(0, 12).join(' ') : ''));
}
// C2: one cluster: every point misses one petal (triple cells t) or two (pair cells p); symmetric family 3t + 3p = k
{
  const out = [];
  for (let t = 0; 3 * t <= k; t++) {
    const rem = k - 3 * t; if (rem % 3) continue; const p = rem / 3;
    const r = quadWin(g, [7, 11, 13, 14, 3, 5, 9, 6, 10, 12], [t, t, t, t, p, p, p, p, p, p]);
    out.push(`(triple cells ${t}, pair cells ${p}; pairwise overlap ${2 * t + p}): ${r ? 'R' : 'A'}`);
  }
  for (let t = 1; 3 * t <= k; t++) {
    const r = quadWin(g, [7, 11, 13, 14], [t, t, t, t]);
    out.push(`(triple cells ${t} only, rest singles; pairwise overlap ${2 * t}): ${r ? 'R' : 'A'}`);
  }
  console.log('C2 one-cluster configurations: ' + out.join('  '));
}
// C3: three cluster petals 1,2,3 with common core c3 and pair-only cells q each, outside petal 4 with one point in each
{
  const rowsR = [];
  for (let c3 = 0; c3 <= k; c3++) {
    let line = '';
    for (let q = 0; c3 + 2 * q + 1 <= k; q++) {
      const r = quadWin(g, [7, 3, 5, 6, 9, 10, 12, 8], [c3, q, q, q, 1, 1, 1, k - 3]);
      line += r ? 'R' : 'A';
    }
    if (line) rowsR.push(`c3=${c3}: ${line}`);
  }
  console.log(`C3 three cluster petals (core c3; columns pair-only cells q = 0,1,2,..) + outside petal: ` + rowsR.join(' | ') + `   [necessary bound from TWIN 15.5: c3 <= T - k/3 = ${(T - k / 3).toFixed(2)}]`);
}
console.log(`  (four-petal configurations evaluated: ${quadCache.size}, engine time ${(quadTime / 1000).toFixed(0)}s)`);
