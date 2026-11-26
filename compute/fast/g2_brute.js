// brute-force validation of g2.js on actual point sets (same game, no type aggregation / symmetry / monotone-sum reduction)
'use strict';
const { makeSolver } = require('./g2.js');
function brute(k, T, a, betas, M, five, strict) {
  const S = makeSolver(k, T, a, betas, M, five, strict);
  const n = 3 * k - a;
  const inA = p => p < k, inA2 = p => p >= k - a && p < 2 * k - a, inF = p => p >= 2 * k - a;
  const base = [], ptsA = [], ptsA2 = [];
  let m0 = 0, m1 = 0, m2 = 0;
  for (let p = 0; p < n; p++) { if (inA(p)) m0 |= 1 << p; if (inA2(p)) m1 |= 1 << p; if (inF(p)) m2 |= 1 << p; }
  const replies0 = [m0, m1, m2];
  const band = []; const fpts = [];
  for (let p = 0; p < n; p++) { if (inA(p) !== inA2(p)) band.push(p); if (inF(p)) fpts.push(p); }
  const maxJ = five ? M - 2 : M - 3;
  const subsets = (arr, size) => { const out = []; (function rec(i, cur) { if (cur.length === size) { out.push(cur.slice()); return; } if (i === arr.length) return; if (arr.length - i < size - cur.length) return; cur.push(arr[i]); rec(i + 1, cur); cur.pop(); rec(i + 1, cur); })(0, []); return out; };
  const allPts = [...Array(n).keys()];
  function typesOf(reps) { const mp = new Map(); for (let p = 0; p < n; p++) { let m = 0; reps.forEach((r, i) => { if ((r >> p) & 1) m |= 1 << i; }); if (m) mp.set(m, (mp.get(m) || 0) + 1); } return [...mp.entries()]; }
  function win(reps, j) {
    if (S.leaf(typesOf(reps), j)) return true;
    if (j >= maxJ) return false;
    for (const sz of [Math.min(T, n)]) for (const req of subsets(allPts, sz)) {       // all requests of size T (monotone in size is itself validated separately below)
      let rm = 0; for (const p of req) rm |= 1 << p;
      const freeBand = band.filter(p => !((rm >> p) & 1)), freeF = fpts.filter(p => !((rm >> p) & 1));
      let ok = true;
      for (const beta of betas) {
        if (freeBand.length < beta || freeF.length < k - beta) continue;
        for (const bs of subsets(freeBand, beta)) { if (!ok) break; for (const fs of subsets(freeF, k - beta)) {
          let e = 0; for (const p of bs) e |= 1 << p; for (const p of fs) e |= 1 << p;
          if (!win(reps.concat([e]), j + 1)) { ok = false; break; }
        } }
        if (!ok) break;
      }
      if (ok) return true;
    }
    return false;
  }
  return win(replies0, 0);
}
let bad = 0, tot = 0;
const cfgs = [];
for (const k of (process.env.KS||"4,5,6").split(",").map(Number)) for (let T = 2; T <= k - 1; T++) for (let a = 1; a < k; a++) for (const betas of [[1], [1, 2]]) for (const M of [5, 6]) for (const five of [false, true]) cfgs.push([k, T, a, betas, M, five]);
const filt = process.argv[2] ? +process.argv[2] : 1e9;
let cnt = 0, rcount = 0;
for (const [k, T, a, betas, M, five] of cfgs) {
  if (T < 2 || cnt++ >= filt) continue;
  const t0 = Date.now();
  const r1 = makeSolver(k, T, a, betas, M, five, true).win0();
  const r2 = brute(k, T, a, betas, M, five, true);
  tot++; if (r1) rcount++;
  if (r1 !== r2) { bad++; console.log('MISMATCH', { k, T, a, betas, M, five, fast: r1, brute: r2 }); }
}
console.log(`g2 vs brute force: ${tot} configurations (${rcount} requester wins), mismatches ${bad}`);
