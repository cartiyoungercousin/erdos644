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

// items: array of codes  mask*64 + count
function canon(masks, counts, n, i) {
  let best = null;
  const maps = PERMS[i];
  const tmp = new Array(n);
  for (let q = 0; q < maps.length; q++) {
    const mp = maps[q];
    for (let j = 0; j < n; j++) tmp[j] = mp[masks[j]] * 64 + counts[j];
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
    for (let B = 0; B <= all; B++) {
      let cost = 0;
      for (let j = 0; j < n; j++) if ((B >> j) & 1) cost += cnt[j];
      if (cost > T) continue;
      const theta = all & ~B;
      if (popc(theta) > k) return null;
      let nb = 0;
      for (let j = 0; j < n; j++) if ((theta >> j) & 1) nb |= adj[j];
      let dn = 0, uOut = 0;
      const outT = theta & ~nb;
      for (let j = 0; j < n; j++) { if ((nb >> j) & 1) dn += cnt[j]; if ((outT >> j) & 1) uOut += cnt[j]; }
      const tIn = popc(theta & nb), nOut = popc(outT);
      const uLeft = Math.max(nOut, uOut - (T - cost));
      const d6 = dn + Math.min(k - tIn, uLeft);
      if (d6 <= T) return { block: masks.filter((m, j) => (B >> j) & 1) };
    }
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
    const w = new Array(n).fill(0);
    for (let a = 0; a < n; a++) {
      const need = full & ~masks[a];
      for (let b = 0; b < n; b++) if ((masks[b] & need) === need) w[a] += cnt[b];
    }
    const reqs = vectors(cnt, T);
    const score = s => { let x = 0; for (let j = 0; j < n; j++) x += s[j] * w[j]; return x; };
    reqs.sort((a, b) => score(b) - score(a));
    let result = false;
    for (const s of reqs) {
      let ok = true;
      for (const ch of this.children(state, i, s)) {
        if (ch.tot <= T) continue;
        if (i + 1 === 6) { ok = false; break; }
        if (!this.win(ch.code, i + 1)) { ok = false; break; }
      }
      if (this.timedOut) return false;
      if (ok) { result = true; this.best.set(key, { req: s.slice() }); break; }
    }
    this.memo.set(key, result);
    return result;
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

const k = parseInt(process.argv[2]);
const Ts = process.argv[3].split(',').map(x => parseInt(x));
const limit = process.argv[4] ? parseFloat(process.argv[4]) : 1150;
for (const T of Ts) {
  const t0 = Date.now();
  const g = new Game(k, T);
  g.deadline = t0 + limit * 1000;
  const r = g.win(g.root(), 1);
  const secs = ((Date.now() - t0) / 1000).toFixed(1);
  if (g.timedOut) { console.log(`k=${k} T=${T} (T/k=${(T / k).toFixed(4)}): UNDECIDED (time limit ${limit}s)  states=${g.memo.size}`); continue; }
  console.log(`k=${k} T=${T} (T/k=${(T / k).toFixed(4)}): ${r ? 'REQUESTER wins' : 'ADVERSARY wins'}   states=${g.memo.size}  [${secs}s]`);
  if (r) for (const ln of mainLine(g)) console.log(ln);
}
