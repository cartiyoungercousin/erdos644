// G2/G3 (TWIN 19.6): re-selection game after a dominant pair.  Ground set: A, A' (|A n A'| = a), F disjoint from A u A'.
// Adversary restricted to MIXED replies: E has exactly k-beta points of F and beta points of (A xor A') (beta in B), all
// outside the request.  Requester: free requests of <= T points, any number of discards (she selects afterwards).
// Leaf (budget M further requests in total after the triple): some 4 replies (triple-free if strict) such that the
// exact confined four-petal game (3 more requests) is a requester win [needs j+3 <= M], or (G3) some 5 replies with
// the exact five-petal game (2 more requests) a requester win [needs j+2 <= M].  Exact engine = engine.js.
// usage: node g2.js k T a betas(comma) M mode(quad|five) [strict=1] [brute]
'use strict';
const { Engine } = require('./engine.js');

function makeSolver(k, T, a, betas, M, five, strict) {
  const FREE = betas === 'free';
  const eng = new Engine(k, T);
  const leafCache = new Map();
  let stuck = 0;
  // types: arrays of [mask,count]; nr = number of replies (3 + j)
  function evalSub(types, sub) {                        // sub: list of reply indices
    const q = sub.length, mk = [], ct = [];
    const full = (1 << q) - 1;
    const map = new Map();
    for (const [m, c] of types) {
      let v = 0;
      for (let b = 0; b < q; b++) if ((m >> sub[b]) & 1) v |= 1 << b;
      if (!v) continue;
      if (strict && q === 4 && (v & (v - 1)) && popc(v) >= 3) return null;       // triple point: not triple-free
      map.set(v, (map.get(v) || 0) + c);
    }
    const ms = [...map.keys()];
    for (const m of ms) {
      const need = full & ~m; let ok = false;
      for (const m2 of ms) if ((m2 & need) === need) { ok = true; break; }
      if (ok) { mk.push(m); ct.push(map.get(m)); }
    }
    if (!mk.length) return true;
    const code = eng.canonArr(mk, ct, q);
    let tot = 0; for (const c of code) tot += c & 63;
    if (tot <= T) return true;
    const key = q + ':' + code.join(',');
    let r = leafCache.get(key);
    if (r === undefined) { r = eng.win(Int32Array.from(code), code.length, q); leafCache.set(key, r); }
    return r;
  }
  function popc(x) { let c = 0; while (x) { x &= x - 1; c++; } return c; }
  function leaf(types, j) {
    const nr = 3 + j;
    if (j + 3 <= M) {
      for (let a1 = 0; a1 < nr; a1++) for (let b1 = a1 + 1; b1 < nr; b1++) for (let c1 = b1 + 1; c1 < nr; c1++) for (let d1 = c1 + 1; d1 < nr; d1++) {
        const r = evalSub(types, [a1, b1, c1, d1]);
        if (r === true) return true;
      }
    }
    if (five && j + 2 <= M && nr >= 5) {
      const rec = (start, sub) => {
        if (sub.length === 5) return evalSub(types, sub) === true;
        for (let x = start; x < nr; x++) { sub.push(x); if (rec(x + 1, sub)) return true; sub.pop(); }
        return false;
      };
      if (rec(0, [])) return true;
    }
    return false;
  }
  function canonKey(types, nr) {
    // symmetries: swap bits 0,1; permute reply bits 3..nr-1
    const E = []; for (let b = 3; b < nr; b++) E.push(b);
    const perms = permsOf(E);
    let best = null;
    for (const sw of [0, 1]) for (const p of perms) {
      const arr = types.map(([m, c]) => {
        let v = m & 4;
        let ab = m & 3; if (sw) ab = ((ab & 1) << 1) | (ab >> 1);
        v |= ab;
        for (let i = 0; i < E.length; i++) if ((m >> E[i]) & 1) v |= 1 << p[i];
        return v * 64 + c;
      }).sort((x, y) => x - y);
      const s = arr.join(',');
      if (best === null || s < best) best = s;
    }
    return nr + '|' + best;
  }
  const PERMC = new Map();
  function permsOf(E) {
    const key = E.length; let r = PERMC.get(key); if (r) return r;
    const out = [];
    (function rec(cur, rest) { if (!rest.length) { out.push(cur.slice()); return; } for (let i = 0; i < rest.length; i++) { cur.push(rest[i]); rec(cur, rest.slice(0, i).concat(rest.slice(i + 1))); cur.pop(); } })([], E);
    PERMC.set(key, out); return out;
  }
  const memo = new Map();
  let nodes = 0;
  function vectors(caps, total) {
    const n = caps.length, out = [], cur = new Array(n).fill(0);
    const suf = new Array(n + 1).fill(0); for (let i = n - 1; i >= 0; i--) suf[i] = suf[i + 1] + caps[i];
    (function rec(i, rem) { if (i === n) { if (rem === 0) out.push(cur.slice()); return; } const lo = Math.max(0, rem - suf[i + 1]), hi = Math.min(caps[i], rem); for (let v = hi; v >= lo; v--) { cur[i] = v; rec(i + 1, rem - v); } cur[i] = 0; })(0, total);
    return out;
  }
  function win(types, j) {                               // types: [[mask,count]...]; replies so far 3+j; budget check inside
    const nr = 3 + j;
    types = types.filter(t => t[1] > 0);
    if (leaf(types, j)) return true;
    if (j >= (five ? M - 2 : M - 3)) return false;      // no further reply can help (budget)
    const key = canonKey(types, nr);
    const mm = memo.get(key); if (mm !== undefined) return mm;
    nodes++;
    const n = types.length, cnt = types.map(t => t[1]);
    let tot = 0; for (const c of cnt) tot += c;
    const reqs = vectors(cnt, Math.min(T, tot));
    const bit = 1 << nr;
    let result = false;
    for (const s of reqs) {
      const rest = cnt.map((c, x) => c - s[x]);
      const bandIdx = [], fIdx = [];
      for (let x = 0; x < n; x++) { const m = types[x][0]; if (((m & 3) === 1 || (m & 3) === 2) && !(m & 4)) bandIdx.push(x); if (m & 4) fIdx.push(x); }
      const bandCap = bandIdx.reduce((u, x) => u + rest[x], 0), fCap = fIdx.reduce((u, x) => u + rest[x], 0);
      let ok = true, any = false;
      if (FREE) {
        any = true;
        let U = 0; for (let x = 0; x < n; x++) U += rest[x];
        const reps = [];
        { const cur = new Array(n).fill(0);
          (function rec(x, used) { if (x === n) { reps.push(cur.slice()); return; } const hi = Math.min(rest[x], k - used); for (let v = hi; v >= 0; v--) { cur[x] = v; rec(x + 1, used + v); } cur[x] = 0; })(0, 0); }
        for (const take of reps) {
          let used = 0; for (let x = 0; x < n; x++) used += take[x];
          const mg = new Map();
          for (let x = 0; x < n; x++) {
            const [m, c] = types[x];
            if (take[x]) mg.set(m | bit, (mg.get(m | bit) || 0) + take[x]);
            if (c - take[x]) mg.set(m, (mg.get(m) || 0) + c - take[x]);
          }
          if (k - used) mg.set(bit, k - used);
          if (!win([...mg.entries()], j + 1)) { ok = false; break; }
        }
      }
      if (!FREE) for (const beta of betas) {
        if (bandCap < beta || fCap < k - beta) continue;
        any = true;
        const bv = vectors(bandIdx.map(x => rest[x]), beta), fv = vectors(fIdx.map(x => rest[x]), k - beta);
        for (const b1 of bv) { if (!ok) break; for (const f1 of fv) {
          const take = new Array(n).fill(0);
          bandIdx.forEach((x, i) => { take[x] = b1[i]; }); fIdx.forEach((x, i) => { take[x] = f1[i]; });
          const nt = [];
          for (let x = 0; x < n; x++) {
            const [m, c] = types[x];
            if (take[x]) nt.push([m | bit, take[x]]);
            if (c - take[x]) nt.push([m, c - take[x]]);
          }
          // merge equal masks
          const mg = new Map(); for (const [m, c] of nt) mg.set(m, (mg.get(m) || 0) + c);
          if (!win([...mg.entries()], j + 1)) { ok = false; break; }
        } }
      }
      if (!any) stuck++;
      if (ok) { result = true; break; }
    }
    memo.set(key, result);
    return result;
  }
  function root() {
    // masks: A=1, A'=2, F=4
    const fA = +process.env.FA || 0, fB = +process.env.FB || 0;
    return [[3, a], [1, k - a - fA], [2, k - a - fB], [5, fA], [6, fB], [4, k - fA - fB]];
  }
  return { leaf, win, root, stats: () => ({ nodes, memo: memo.size, leaf: leafCache.size, stuck, engineNodes: eng.nodes }), win0: () => win(root(), 0) };
}

module.exports = { makeSolver };

if (require.main === module) {
  const [k, T, a, betaS, M, mode] = [+process.argv[2], +process.argv[3], +process.argv[4], process.argv[5], +process.argv[6], process.argv[7]];
  const strict = process.argv[8] !== '0';
  const betas = betaS === 'free' ? 'free' : betaS.split(',').map(Number);
  const s = makeSolver(k, T, a, betas, M, mode === 'five', strict);
  const t0 = Date.now();
  const r = s.win0();
  console.log(`G2/G3 k=${k} T=${T} a=${a} betas=[${betas}] M=${M} mode=${mode} strict=${strict}: ${r ? 'REQUESTER wins' : 'ADVERSARY wins'}  ${JSON.stringify(s.stats())} [${((Date.now() - t0) / 1000).toFixed(1)}s]`);
}
