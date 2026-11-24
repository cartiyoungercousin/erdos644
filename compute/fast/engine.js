// Fast exact engine for the confined request game (same semantics as compute/fresh_c/exact7d.js, anchor.js,
// anchor_select.js, exact7N.js).  State = multiset of membership types (mask*64+count) of the points of D,
// canonical under relabelling of the i existing edges.  Differences from the originals (none affects semantics):
//  * typed arrays everywhere, integer edge invariants (no strings), O(n) relevance filter via superset bitsets;
//  * transposition table = open-addressing hash over a Uint16 pool holding the FULL key (no hash-collision risk),
//    reset when over its entry cap (correctness unaffected);
//  * killer replies: refuting adversary replies of a node are retried first against later requests;
//  * request ordering by counting sort on the same heuristic score; moves for certificates are re-derived on demand.
'use strict';

const POPC = new Uint8Array(64);
for (let m = 1; m < 64; m++) POPC[m] = POPC[m >> 1] + (m & 1);
const SUPLO = new Int32Array(64), SUPHI = new Int32Array(64);
for (let need = 0; need < 64; need++) for (let m = 0; m < 64; m++) if ((m & need) === need) {
  if (m < 32) SUPLO[need] |= 1 << m; else SUPHI[need] |= 1 << (m - 32);
}
function permutations(arr) {
  if (arr.length <= 1) return [arr.slice()];
  const out = [];
  for (let i = 0; i < arr.length; i++) {
    const rest = arr.slice(0, i).concat(arr.slice(i + 1));
    for (const p of permutations(rest)) out.push([arr[i]].concat(p));
  }
  return out;
}
// pseudo-random hash tables (any isomorphism-invariant function is fine for the canonical form)
const HF = new Int32Array(64 * 64), HG = new Int32Array(64);
{
  let x = 123456789; const nx = () => { x ^= x << 13; x ^= x >>> 17; x ^= x << 5; return x | 0; };
  for (let i = 0; i < HF.length; i++) HF[i] = nx();
  for (let i = 0; i < 64; i++) HG[i] = nx();
}

const ORDERS = new Map();
function getOrders(sizes) {                 // sizes of tie groups, in sorted order -> flat Int8Array of orderings
  let key = 0; for (const s of sizes) key = key * 8 + s;
  let r = ORDERS.get(key); if (r) return r;
  let acc = [[]], off = 0;
  for (const g of sizes) {
    const ps = permutations([...Array(g).keys()].map(x => x + off));
    const next = [];
    for (const a of acc) for (const p of ps) next.push(a.concat(p));
    acc = next; off += g;
  }
  const flat = new Int8Array(acc.length * off);
  acc.forEach((a, t) => a.forEach((v, p) => { flat[t * off + p] = v; }));
  r = { flat, count: acc.length, len: off };
  ORDERS.set(key, r); return r;
}
const _size = new Int32Array(8), _h1 = new Int32Array(8), _inter = new Int32Array(64), _inv = new Float64Array(8);
const _ord = new Int32Array(8), _newpos = new Int32Array(8), _tlo = new Int32Array(8), _thi = new Int32Array(8);
const _tmp = new Int32Array(128);
const _gs = [];
// canonical form: minimum over all relabellings consistent with the (isomorphism-invariant) edge order.  ie <= 6.
function canonInto(mk, ct, n, ie, out) {
  _size.fill(0, 0, ie); _h1.fill(0, 0, ie); _inter.fill(0, 0, 64);
  for (let x = 0; x < n; x++) {
    const m = mk[x], c = ct[x], h = HF[POPC[m] * 64 + c];
    for (let b = 0; b < ie; b++) if ((m >> b) & 1) {
      _size[b] += c; _h1[b] = (_h1[b] + h) | 0;
      for (let d = 0; d < ie; d++) if (d !== b && ((m >> d) & 1)) _inter[b * 8 + d] += c;
    }
  }
  for (let b = 0; b < ie; b++) {
    let h2 = 0;
    for (let d = 0; d < ie; d++) if (d !== b) h2 = (h2 + HG[_inter[b * 8 + d]]) | 0;
    let z = Math.imul(_h1[b] ^ 0x5bd1e995, 0x85ebca6b) ^ h2; z = Math.imul(z ^ (z >>> 15), 0xc2b2ae35); z ^= z >>> 13;
    _inv[b] = _size[b] * 4294967296 + (z >>> 0);
  }
  for (let b = 0; b < ie; b++) _ord[b] = b;
  for (let a = 1; a < ie; a++) { const v = _ord[a]; let p = a - 1; while (p >= 0 && _inv[_ord[p]] > _inv[v]) { _ord[p + 1] = _ord[p]; p--; } _ord[p + 1] = v; }
  _gs.length = 0;
  for (let p = 0; p < ie; p++) { if (p > 0 && _inv[_ord[p]] === _inv[_ord[p - 1]]) _gs[_gs.length - 1]++; else _gs.push(1); }
  const O = getOrders(_gs);
  let have = false;
  for (let t = 0; t < O.count; t++) {
    for (let p = 0; p < ie; p++) _newpos[_ord[O.flat[t * ie + p]]] = p;
    for (let q = 0; q < 8; q++) {
      let lo = 0, hi = 0;
      for (let b = 0; b < 3; b++) if ((q >> b) & 1) { if (b < ie) lo |= 1 << _newpos[b]; if (b + 3 < ie) hi |= 1 << _newpos[b + 3]; }
      _tlo[q] = lo; _thi[q] = hi;
    }
    for (let x = 0; x < n; x++) { const m = mk[x]; _tmp[x] = (_tlo[m & 7] | _thi[m >> 3]) * 64 + ct[x]; }
    for (let a = 1; a < n; a++) { const v = _tmp[a]; let p = a - 1; while (p >= 0 && _tmp[p] > v) { _tmp[p + 1] = _tmp[p]; p--; } _tmp[p + 1] = v; }
    if (!have) { for (let x = 0; x < n; x++) out[x] = _tmp[x]; have = true; continue; }
    for (let x = 0; x < n; x++) {
      if (_tmp[x] < out[x]) { for (let y = x; y < n; y++) out[y] = _tmp[y]; break; }
      if (_tmp[x] > out[x]) break;
    }
  }
}

// ---- exact-key hash table
class Table {
  constructor(maxEntries) { this.max = maxEntries; this.resets = 0; this.reset(); }
  reset() {
    this.cap = 1 << 16; this.slots = new Uint32Array(this.cap);
    this.pool = new Uint16Array(1 << 18); this.top = 0; this.count = 0; this.resets++;
  }
  hash(codes, n, i) {
    let h = Math.imul(i + 1, 0x9E3779B1);
    for (let x = 0; x < n; x++) { h = Math.imul(h ^ codes[x], 0x85EBCA6B); h ^= h >>> 15; }
    return h >>> 0;
  }
  get(codes, n, i) {
    const mask = this.cap - 1, pool = this.pool, slots = this.slots;
    let s = this.hash(codes, n, i) & mask;
    for (;;) {
      const o = slots[s];
      if (o === 0) return -1;
      const hd = pool[o - 1];
      if ((hd & 127) === n && ((hd >> 8) & 15) === i) {
        let x = 0; while (x < n && pool[o + x] === codes[x]) x++;
        if (x === n) return (hd >> 7) & 1;
      }
      s = (s + 1) & mask;
    }
  }
  set(codes, n, i, val) {
    if (this.count >= this.max) this.reset();
    if (this.count * 2 >= this.cap) this.grow();
    if (this.top + n + 2 > this.pool.length) { const np = new Uint16Array(this.pool.length * 2); np.set(this.pool); this.pool = np; }
    const mask = this.cap - 1;
    let s = this.hash(codes, n, i) & mask;
    while (this.slots[s] !== 0) s = (s + 1) & mask;
    const o = this.top + 1;
    this.pool[this.top] = n | (val << 7) | (i << 8);
    for (let x = 0; x < n; x++) this.pool[o + x] = codes[x];
    this.slots[s] = o; this.top = o + n; this.count++;
  }
  grow() {
    const ncap = this.cap * 2, ns = new Uint32Array(ncap), mask = ncap - 1, pool = this.pool;
    for (let s = 0; s < this.cap; s++) {
      const o = this.slots[s]; if (!o) continue;
      const hd = pool[o - 1], n = hd & 127, i = (hd >> 8) & 15;
      let t = this.hash(pool.subarray(o, o + n), n, i) & mask;
      while (ns[t] !== 0) t = (t + 1) & mask;
      ns[t] = o;
    }
    this.slots = ns; this.cap = ncap;
  }
}

function popc32(x) { x = x - ((x >>> 1) & 0x55555555); x = (x & 0x33333333) + ((x >>> 2) & 0x33333333); return (((x + (x >>> 4)) & 0x0F0F0F0F) * 0x01010101) >>> 24; }

class Frame {
  constructor() {
    this.codes = new Int32Array(40); this.mk = new Int32Array(40); this.ct = new Int32Array(40);
    this.w = new Int32Array(40); this.ordT = new Int32Array(40); this.rest = new Int32Array(40);
    this.a = new Int32Array(40); this.cur = new Int32Array(40); this.suffix = new Int32Array(41);
    this.kill = new Int32Array(40 * 8); this.nkill = 0;
    this.req = new Int8Array(40 * 1024); this.nreq = 0;
    this.n = 0; this.tot = 0; this.i = 0;
  }
}

class Engine {
  constructor(k, T, opts) {
    opts = opts || {};
    this.k = k; this.T = T;
    this.t34 = new Table(opts.maxEntries || 20e6);
    this.t5 = new Table(opts.maxEntries5 || 20e6);
    this.deadline = Infinity; this.timedOut = false; this.tick = 0;
    this.usePairBound = opts.pairBound !== false;
    this.pruned = 0; this.nodes = 0;
    this.frames = []; for (let i = 0; i < 8; i++) this.frames.push(new Frame());
    this.scratchM = new Int32Array(128); this.scratchC = new Int32Array(128);
    this.childBuf = []; for (let i = 0; i < 8; i++) this.childBuf.push(new Int32Array(128));
    this.recordMove = false; this.move = null;
    this.blockB = 0;
    this.fastLast = opts.fastLast !== false; this.sfx5 = new Int32Array(48); this.kill5 = new Array(8).fill(0);
    this.adj = new Int32Array(40);
    this.deg = new Int32Array(40); this.ordD = new Int32Array(40);
  }
  states() { return this.t34.count + this.t5.count; }
  // closed-form last round, identical to the originals; returns 1/0, or -1 for "bail" (fall back to search)
  lastRound(mk, ct, n) {
    const k = this.k, T = this.T, adj = this.adj;
    for (let a = 0; a < n; a++) {
      const need = 31 & ~mk[a]; let r = 0;
      for (let b = 0; b < n; b++) if ((mk[b] & need) === need) r |= 1 << b;
      adj[a] = r;
    }
    const all = (1 << n) - 1;
    let found = -2, bail = false;
    const rec = (j, B, cost) => {
      if (found !== -2 || bail) return;
      if (j === n) {
        const theta = all & ~B;
        if (popc32(theta) > k) { bail = true; return; }
        let nb = 0;
        for (let x = 0; x < n; x++) if ((theta >> x) & 1) nb |= adj[x];
        let dn = 0, uOut = 0;
        const outT = theta & ~nb;
        for (let x = 0; x < n; x++) { if ((nb >> x) & 1) dn += ct[x]; if ((outT >> x) & 1) uOut += ct[x]; }
        const tIn = popc32(theta & nb), nOut = popc32(outT);
        const uLeft = Math.max(nOut, uOut - (T - cost));
        const d6 = dn + Math.min(k - tIn, uLeft);
        if (d6 <= T) found = B;
        return;
      }
      if (cost + ct[j] <= T) rec(j + 1, B | (1 << j), cost + ct[j]);
      rec(j + 1, B, cost);
    };
    rec(0, 0, 0);
    if (bail && found === -2) return -1;
    if (found !== -2) { this.blockB = found; return 1; }
    return 0;
  }
  pairBound(F, n, i, tot, rho) {
    const k = this.k, T = this.T, mk = F.mk, ct = F.ct, deg = this.deg, ord = this.ordD;
    const full = (1 << i) - 1;
    let P2 = 0;
    for (let a = 0; a < n; a++) {
      const need = full & ~mk[a]; let d = 0;
      for (let b = 0; b < n; b++) if ((mk[b] & need) === need) d += ct[b];
      if (mk[a] === full) d += 1;
      deg[a] = d; P2 += d * ct[a]; ord[a] = a;
    }
    for (let a = 1; a < n; a++) { const v = ord[a]; let p = a - 1; while (p >= 0 && deg[ord[p]] < deg[v]) { ord[p + 1] = ord[p]; p--; } ord[p + 1] = v; }
    const kap = q => {
      let rem = q, sum = 0;
      for (let x = 0; x < n; x++) { const j = ord[x]; const t = Math.min(rem, ct[j]); sum += t * deg[j]; rem -= t; if (!rem) break; }
      return Math.min(sum / 2, q * (q - 1) / 2 + q);
    };
    const q = Math.max(T, tot - k);
    return P2 / 2 > rho * kap(q) + kap(T) + 1e-9;
  }
  // child after reply a at frame F (i edges -> i+1).  returns n2 >= 0 (canonical child in `out`), -1 if |D'| <= T
  // (requester wins), -2 if i+1 == 6 and |D'| > T (adversary wins).
  child(F, a, out) {
    const n = F.n, mk = F.mk, ct = F.ct, i = F.i, T = this.T, b = 1 << i, full1 = (1 << (i + 1)) - 1;
    const im = this.scratchM, ic = this.scratchC;
    let m = 0, lo = 0, hi = 0;
    for (let j = 0; j < n; j++) {
      const aj = a[j], r = ct[j] - aj, mm = mk[j];
      if (aj) { const q = mm | b; im[m] = q; ic[m++] = aj; if (q < 32) lo |= 1 << q; else hi |= 1 << (q - 32); }
      if (r) { im[m] = mm; ic[m++] = r; if (mm < 32) lo |= 1 << mm; else hi |= 1 << (mm - 32); }
    }
    let n2 = 0, tot2 = 0;
    const rm = this.childBuf[7], rc = this.childBuf[6];
    for (let x = 0; x < m; x++) {
      const need = full1 & ~im[x];
      if ((lo & SUPLO[need]) !== 0 || (hi & SUPHI[need]) !== 0) { rm[n2] = im[x]; rc[n2++] = ic[x]; tot2 += ic[x]; }
    }
    if (tot2 <= T) return -1;
    if (i + 1 === 6) return -2;
    canonInto(rm, rc, n2, i + 1, out);
    return n2;
  }
  // does the requester win from this canonical state with i edges?
  win(codes, n, i) {
    const rec = this.recordMove; this.recordMove = false;
    const T = this.T;
    let tot = 0;
    for (let x = 0; x < n; x++) tot += codes[x] & 63;
    if (tot <= T) return true;
    if (i === 6) return false;
    const tbl = i === 5 ? this.t5 : this.t34;
    if (!rec) {
      const v = tbl.get(codes, n, i);
      if (v >= 0) return v === 1;
    }
    if (this.timedOut) return false;
    if ((++this.tick & 1023) === 0 && Date.now() > this.deadline) { this.timedOut = true; return false; }
    this.nodes++;
    const F = this.frames[i];
    F.n = n; F.i = i; F.tot = tot;
    for (let x = 0; x < n; x++) { F.codes[x] = codes[x]; F.mk[x] = codes[x] >> 6; F.ct[x] = codes[x] & 63; }
    const mk = F.mk, ct = F.ct;
    if (i === 5 && this.fastLast && tot - T <= this.k) return this.forced5(F, n, tbl, rec);
    if (i === 5) {
      const r = this.lastRound(mk, ct, n);
      if (r >= 0) {
        tbl.set(F.codes, n, i, r);
        if (rec && r === 1) { const blk = []; for (let x = 0; x < n; x++) if ((this.blockB >> x) & 1) blk.push(mk[x]); this.move = { block: blk }; }
        return r === 1;
      }
    }
    if (this.usePairBound && this.pairBound(F, n, i, tot, 6 - i)) { tbl.set(F.codes, n, i, 0); this.pruned++; return false; }
    if (i === 5 && this.fastLast) return this.win5(F, n, tbl, rec);
    const k = this.k, w = F.w, full = (1 << i) - 1;
    for (let a = 0; a < n; a++) {
      const need = full & ~mk[a]; let s = 0;
      for (let b = 0; b < n; b++) if ((mk[b] & need) === need) s += ct[b];
      w[a] = s;
    }
    const ordT = F.ordT;
    for (let x = 0; x < n; x++) ordT[x] = x;
    for (let a = 1; a < n; a++) { const v = ordT[a]; let p = a - 1; while (p >= 0 && w[ordT[p]] < w[v]) { ordT[p + 1] = ordT[p]; p--; } ordT[p + 1] = v; }
    // requests: all vectors with sum exactly T, bounded by ct
    const suf = F.suffix; suf[n] = 0;
    for (let x = n - 1; x >= 0; x--) suf[x] = suf[x + 1] + ct[x];
    let nreq = 0; let req = F.req;
    const cur = F.cur;
    const gen = (j, remain) => {
      if (j === n) {
        if (remain === 0) {
          if ((nreq + 1) * n > req.length) { const nr = new Int8Array(req.length * 2); nr.set(req); req = F.req = nr; }
          for (let x = 0; x < n; x++) req[nreq * n + x] = cur[x];
          nreq++;
        }
        return;
      }
      const lo = Math.max(0, remain - suf[j + 1]), hi = Math.min(ct[j], remain);
      for (let v = hi; v >= lo; v--) { cur[j] = v; gen(j + 1, remain - v); }
      cur[j] = 0;
    };
    gen(0, T);
    F.nreq = nreq;
    // counting sort by score descending (score = sum s_j w_j), as in the originals
    let maxS = 0;
    const sc = new Int32Array(nreq);
    for (let q = 0; q < nreq; q++) { let s = 0; for (let x = 0; x < n; x++) s += req[q * n + x] * w[x]; sc[q] = s; if (s > maxS) maxS = s; }
    const cntS = new Int32Array(maxS + 2);
    for (let q = 0; q < nreq; q++) cntS[maxS - sc[q] + 1]++;
    for (let s = 0; s <= maxS; s++) cntS[s + 1] += cntS[s];
    const order = new Int32Array(nreq);
    for (let q = 0; q < nreq; q++) order[cntS[maxS - sc[q]]++] = q;
    F.nkill = 0;
    const rest = F.rest, a = F.a, kill = F.kill;
    const out = this.childBuf[i];
    let result = false;
    const self = this;
    const test = () => {            // true iff the requester still wins against the reply in `a`
      const n2 = self.child(F, a, out);
      if (n2 === -1) return true;
      if (n2 === -2) return false;
      return self.win(out, n2, i + 1);
    };
    for (let oq = 0; oq < nreq && !result; oq++) {
      const q = order[oq], base = q * n;
      let U = 0;
      for (let x = 0; x < n; x++) { rest[x] = ct[x] - req[base + x]; U += rest[x]; }
      let ok = true;
      if (U <= k) {
        for (let x = 0; x < n; x++) a[x] = rest[x];
        ok = test();
      } else {
        for (let kk = 0; kk < F.nkill && ok; kk++) {                 // killer replies first
          const o = kk * n; let feas = true;
          for (let x = 0; x < n; x++) if (kill[o + x] > rest[x]) { feas = false; break; }
          if (!feas) continue;
          for (let x = 0; x < n; x++) a[x] = kill[o + x];
          if (!test()) {
            ok = false;
            if (kk > 0) for (let x = 0; x < n; x++) { const t = kill[o + x]; kill[o + x] = kill[x]; kill[x] = t; }
          }
          if (this.timedOut) return false;
        }
        if (ok) {
          const sf = F.suffix; sf[n] = 0;
          for (let p = n - 1; p >= 0; p--) sf[p] = sf[p + 1] + rest[ordT[p]];
          const enumr = (p, rem) => {
            if (!ok) return;
            if (p === n) {
              if (rem === 0 && !test()) {
                ok = false;
                if (F.nkill < 8) F.nkill++;
                for (let y = F.nkill - 1; y > 0; y--) for (let x = 0; x < n; x++) kill[y * n + x] = kill[(y - 1) * n + x];
                for (let x = 0; x < n; x++) kill[x] = a[x];
              }
              return;
            }
            const j = ordT[p];
            const lo = Math.max(0, rem - sf[p + 1]), hi = Math.min(rest[j], rem);
            for (let v = hi; v >= lo && ok; v--) { a[j] = v; enumr(p + 1, rem - v); }
            a[j] = 0;
          };
          enumr(0, k);
        }
      }
      if (this.timedOut) return false;
      if (ok) {
        result = true;
        if (rec) { const s = new Array(n); for (let x = 0; x < n; x++) s[x] = req[base + x]; this.move = { req: s }; }
      }
    }
    tbl.set(F.codes, n, i, result ? 1 : 0);
    return result;
  }
  // Exact evaluation of a 5-edge state when the reply is forced (|D| - T <= k: the adversary must take every
  // unrequested point).  The requester wins iff some request leaves |D_6| <= T.  Enumerates the set B of fully
  // requested types; the spare budget r = T - cnt(B) goes to the unrequested types (at least one point stays in each),
  // preferably to those not adjacent to P = types not in B.  Pruned by cnt(N(P_min)) > T.
  forced5(F, n, tbl, rec) {
    const T = this.T, mk = F.mk, ct = F.ct, adj = this.adj;
    for (let a = 0; a < n; a++) {
      const need = 31 & ~mk[a]; let r = 0;
      for (let b = 0; b < n; b++) if ((mk[b] & need) === need) r |= 1 << b;
      adj[a] = r;
    }
    const self = this;
    let foundB = -1;
    const all = n >= 31 ? 0x7fffffff : (1 << n) - 1;
    const nbOf = (P) => { let N = 0; for (let x = 0; x < n; x++) if ((P >> x) & 1) N |= adj[x]; return N; };
    const cntOf = (M) => { let c = 0; for (let x = 0; x < n; x++) if ((M >> x) & 1) c += ct[x]; return c; };
    const dfs = (j, B, cost, Om) => {
      if (foundB >= 0) return;
      // optimistic P: decided-out plus undecided types that cannot be afforded
      let Pmin = Om;
      for (let x = j; x < n; x++) if (cost + ct[x] > T) Pmin |= 1 << x;
      if (Pmin && cntOf(nbOf(Pmin)) > T) return;
      if (j === n) {
        const P = Om;
        if (!P) return;
        const r = T - cost;
        let capAll = 0, capOut = 0, out = 0;
        const N = nbOf(P);
        for (let x = 0; x < n; x++) if ((P >> x) & 1) {
          capAll += ct[x] - 1;
          if (!((N >> x) & 1)) { capOut += ct[x] - 1; out += ct[x]; }
        }
        if (r > capAll) return;
        const V = cntOf(N) + out - Math.min(r, capOut);
        if (V <= T) foundB = B;
        return;
      }
      if (cost + ct[j] <= T) dfs(j + 1, B | (1 << j), cost + ct[j], Om);
      dfs(j + 1, B, cost, Om | (1 << j));
    };
    dfs(0, 0, 0, 0);
    const res = foundB >= 0;
    tbl.set(F.codes, n, 5, res ? 1 : 0);
    if (res && rec) {
      const s = new Array(n).fill(0);
      let cost = 0;
      for (let x = 0; x < n; x++) if ((foundB >> x) & 1) { s[x] = ct[x]; cost += ct[x]; }
      let r = T - cost;
      const P = all & ~foundB, N = nbOf(P);
      for (let x = 0; x < n && r > 0; x++) if (((P >> x) & 1) && !((N >> x) & 1)) { const t = Math.min(r, ct[x] - 1); s[x] += t; r -= t; }
      for (let x = 0; x < n && r > 0; x++) if (((P >> x) & 1) && ((N >> x) & 1)) { const t = Math.min(r, ct[x] - 1); s[x] += t; r -= t; }
      this.move = { req: s };
    }
    return res;
  }
  // |D_6| of the adversary reply with support S (set of types) at a 5-edge state: all points of the types adjacent to
  // S, plus the reply points lying in S-types that are not adjacent to S.  rest = unrequested points per type.
  v5(S, rest, ct, adj, n) {
    let N = 0, cap = 0;
    for (let x = 0; x < n; x++) if ((S >> x) & 1) N |= adj[x];
    let cn = 0;
    for (let x = 0; x < n; x++) { if ((N >> x) & 1) cn += ct[x]; else if ((S >> x) & 1) cap += rest[x]; }
    const t = this.k - popc32(S & N);
    return cn + (cap < t ? cap : t);
  }
  // exists S (support of a reply a <= rest, |a| = k) with |D_6| > T ?  returns S or 0   (case U > k)
  refute5(rest, ct, adj, n, Pm) {
    const k = this.k, T = this.T, self = this;
    let found = 0;
    const sfx = this.sfx5;
    sfx[n] = 0;
    for (let x = n - 1; x >= 0; x--) sfx[x] = sfx[x + 1] + (((Pm >> x) & 1) ? rest[x] : 0);
    const rec = (x, S, sz, sr) => {
      if (found) return;
      if (x === n) {
        if (sz >= 1 && sr >= k && self.v5(S, rest, ct, adj, n) > T) found = S;
        return;
      }
      if (sr + sfx[x] < k) return;
      if (((Pm >> x) & 1) === 0) { rec(x + 1, S, sz, sr); return; }
      if (sz < k) rec(x + 1, S | (1 << x), sz + 1, sr + rest[x]);
      rec(x + 1, S, sz, sr);
    };
    rec(0, 0, 0, 0);
    return found;
  }
  win5(F, n, tbl, rec) {
    const k = this.k, T = this.T, mk = F.mk, ct = F.ct, adj = this.adj;
    for (let a = 0; a < n; a++) {
      const need = 31 & ~mk[a]; let r = 0;
      for (let b = 0; b < n; b++) if ((mk[b] & need) === need) r |= 1 << b;
      adj[a] = r;
    }
    const w = F.w;
    for (let a = 0; a < n; a++) { let s = 0; for (let b = 0; b < n; b++) if ((adj[a] >> b) & 1) s += ct[b]; w[a] = s; }
    const suf = F.suffix; suf[n] = 0;
    for (let x = n - 1; x >= 0; x--) suf[x] = suf[x + 1] + ct[x];
    let nreq = 0; let req = F.req;
    const cur = F.cur;
    const gen = (j, remain) => {
      if (j === n) {
        if (remain === 0) {
          if ((nreq + 1) * n > req.length) { const nr = new Int8Array(req.length * 2); nr.set(req); req = F.req = nr; }
          for (let x = 0; x < n; x++) req[nreq * n + x] = cur[x];
          nreq++;
        }
        return;
      }
      const lo = Math.max(0, remain - suf[j + 1]), hi = Math.min(ct[j], remain);
      for (let v = hi; v >= lo; v--) { cur[j] = v; gen(j + 1, remain - v); }
      cur[j] = 0;
    };
    gen(0, T);
    let maxS = 0;
    const sc = new Int32Array(nreq);
    for (let q = 0; q < nreq; q++) { let s = 0; for (let x = 0; x < n; x++) s += req[q * n + x] * w[x]; sc[q] = s; if (s > maxS) maxS = s; }
    const cntS = new Int32Array(maxS + 2);
    for (let q = 0; q < nreq; q++) cntS[maxS - sc[q] + 1]++;
    for (let s = 0; s <= maxS; s++) cntS[s + 1] += cntS[s];
    const order = new Int32Array(nreq);
    for (let q = 0; q < nreq; q++) order[cntS[maxS - sc[q]]++] = q;
    const rest = F.rest;
    const killS = this.kill5; let nk = 0;
    let result = false;
    for (let oq = 0; oq < nreq && !result; oq++) {
      const q = order[oq], base = q * n;
      let U = 0, Pm = 0;
      for (let x = 0; x < n; x++) { const r = ct[x] - req[base + x]; rest[x] = r; U += r; if (r > 0) Pm |= 1 << x; }
      let ok;
      if (U <= k) ok = this.v5(Pm, rest, ct, adj, n) <= T;
      else {
        ok = true;
        for (let kk = 0; kk < nk; kk++) {
          const S = killS[kk];
          if ((S & ~Pm) !== 0) continue;
          let sr = 0, sz = 0;
          for (let x = 0; x < n; x++) if ((S >> x) & 1) { sr += rest[x]; sz++; }
          if (sr < k || sz > k) continue;
          if (this.v5(S, rest, ct, adj, n) > T) { ok = false; if (kk > 0) { killS[kk] = killS[0]; killS[0] = S; } break; }
        }
        if (ok) {
          const S = this.refute5(rest, ct, adj, n, Pm);
          if (S) { ok = false; if (nk < 8) nk++; for (let y = nk - 1; y > 0; y--) killS[y] = killS[y - 1]; killS[0] = S; }
        }
      }
      if (ok) {
        result = true;
        if (rec) { const s = new Array(n); for (let x = 0; x < n; x++) s[x] = req[base + x]; this.move = { req: s }; }
      }
    }
    tbl.set(F.codes, n, 5, result ? 1 : 0);
    return result;
  }
  // winning move at a state known (or tested) to be a requester win: {req:[...]} or {block:[masks]} or null
  moveFor(codes, n, i) {
    this.recordMove = true; this.move = null;
    const r = this.win(codes, n, i);
    this.recordMove = false;
    return r ? this.move : null;
  }
  // canonical children (distinct, with |D'| > T) of a state under request s, as arrays of codes (i+1 <= 5 or tot only)
  children(codes, n, i, s) {
    const k = this.k, T = this.T;
    const F = new Frame(); F.n = n; F.i = i;
    for (let x = 0; x < n; x++) { F.mk[x] = codes[x] >> 6; F.ct[x] = codes[x] & 63; }
    const rest = new Array(n); let U = 0;
    for (let x = 0; x < n; x++) { rest[x] = F.ct[x] - s[x]; U += rest[x]; }
    const out = new Int32Array(128), seen = new Set(), res = [];
    const a = F.a;
    const emit = () => {
      const n2 = this.child(F, a, out);
      if (n2 >= 0) { const c = Array.from(out.subarray(0, n2)); const key = c.join(','); if (!seen.has(key)) { seen.add(key); res.push(c); } }
    };
    if (U <= k) { for (let x = 0; x < n; x++) a[x] = rest[x]; emit(); return res; }
    const rec = (x, rem) => {
      if (x === n) { if (rem === 0) emit(); return; }
      let sfx = 0; for (let y = x + 1; y < n; y++) sfx += rest[y];
      const lo = Math.max(0, rem - sfx), hi = Math.min(rest[x], rem);
      for (let v = hi; v >= lo; v--) { a[x] = v; rec(x + 1, rem - v); }
      a[x] = 0;
    };
    rec(0, k);
    return res;
  }
  canonArr(masks, counts, ie) {
    const n = masks.length, out = new Int32Array(Math.max(n, 1));
    canonInto(Int32Array.from(masks), Int32Array.from(counts), n, ie, out);
    return Array.from(out.subarray(0, n));
  }
}

module.exports = { Engine, canonInto, POPC, permutations };
