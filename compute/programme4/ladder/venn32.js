// Randomised search for a good seven of a FIXED co-type class inside a G-invariant family on n <= 32 points
// (heuristic: finds, never refutes).  Family = union of orbits, given as representatives + the group elements.
// Class used: co-types = the 7 Fano lines, each with multiplicity mu, plus u points with co-type [7]
// (n = 7 mu + u, block size c = 3 mu + u).  Blocks B_1..B_7 are chosen in order; B_i must meet each Venn region of
// B_1..B_{i-1} in exactly the class's count; the last blocks are forced and tested for membership.
// Input JSON: {n, mu, u, reps:[masks], G:[[perm]], tries, seed}.  Output JSON: {status, seven, orbits}
"use strict";
const fs = require("fs");
const inp = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
const { n, mu, u } = inp; const reps = inp.reps.map(Number); const G = inp.G;
let seed = inp.seed || 12345; const rnd = () => { seed = (seed * 48271) % 2147483647; return seed / 2147483647; };
const bit = x => 2 ** x;
const ptsOf = X => { const p = []; for (let x = 0; x < n; x++) if (Math.floor(X / bit(x)) % 2) p.push(x); return p; };
// members: all images, with orbit index; sorted unique
const mem = new Map();
reps.forEach((r, o) => { const P = ptsOf(r); for (const g of G) { let v = 0; for (const x of P) v += bit(g[x]); if (!mem.has(v)) mem.set(v, o); } });
const M = Float64Array.from(mem.keys()); const MO = Int32Array.from(mem.values());
console.error(`members ${M.length}`);
const lines = [[0, 1, 2], [0, 3, 4], [0, 5, 6], [1, 3, 5], [1, 4, 6], [2, 3, 6], [2, 4, 5]];
const cot = []; for (const L of lines) for (let q = 0; q < mu; q++) cot.push(L.reduce((s, i) => s | (1 << i), 0)); for (let q = 0; q < u; q++) cot.push(127);
if (cot.length !== n) throw new Error("n != 7mu+u");
// required |B_i cap R_S| for pattern S on labels < i: number of co-types t with (t & ((1<<i)-1)) == S and bit i set
const need = []; for (let i = 0; i < 7; i++) { const mp = new Map(); for (const t of cot) if ((t >> i) & 1) { const S = t & ((1 << i) - 1); mp.set(S, (mp.get(S) || 0) + 1); } need.push(mp); }
const pc32 = v => { let lo = v % 65536, hi = Math.floor(v / 65536), r = 0; while (lo) { lo &= lo - 1; r++; } while (hi) { hi &= hi - 1; r++; } return r; };
const and = (a, b) => { const alo = a % 65536, ahi = Math.floor(a / 65536), blo = b % 65536, bhi = Math.floor(b / 65536); return (alo & blo) + 65536 * (ahi & bhi); };
function regions(blocks) { // map pattern -> mask of points
  const R = new Map(); for (let x = 0; x < n; x++) { let S = 0; blocks.forEach((B, i) => { if (Math.floor(B / bit(x)) % 2) S |= 1 << i; }); R.set(S, (R.get(S) || 0) + bit(x)); }
  return R;
}
function fits(B, R, i) { for (const [S, mask] of R) { const want = need[i].get(S) || 0; if (pc32(and(B, mask)) !== want) return false; } return true; }
const tries = inp.tries || 1000; let res = null;
outer: for (let t = 0; t < tries; t++) {
  const o0 = Math.floor(rnd() * reps.length); const blocks = [reps[o0]]; const orbs = [o0];
  let ok = true;
  for (let i = 1; i < 7 && ok; i++) {
    const R = regions(blocks);
    // forced?
    let forced = true, fb = 0; for (const [S, mask] of R) { const w = need[i].get(S) || 0; if (w === pc32(mask)) fb += mask; else if (w !== 0) { forced = false; break; } }
    if (forced) { if (!mem.has(fb)) { ok = false; break; } blocks.push(fb); orbs.push(mem.get(fb)); continue; }
    // random scan from a random start for a fitting member
    const start = Math.floor(rnd() * M.length); let found = -1;
    for (let k = 0; k < M.length; k++) { const j = (start + k) % M.length; if (fits(M[j], R, i)) { found = j; break; } }
    if (found < 0) { ok = false; break; }
    blocks.push(M[found]); orbs.push(MO[found]);
  }
  if (ok) { res = { blocks, orbs, t }; break outer; }
}
console.log(JSON.stringify(res ? { status: "found", seven: res.blocks, orbits: res.orbs, tries: res.t + 1 } : { status: "none" }));
