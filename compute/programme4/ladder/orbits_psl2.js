// Orbits of PSL(2,q) (q prime, q = 3 mod 4, so PSL(2,q) is 3-homogeneous on PG(1,q)) on t-subsets of the q+1 points,
// for t = 0..tmax, by canonical augmentation, plus the inclusion edges t -> t+1 between orbits.
// Canonical form of X: the minimum of g(X) over the |G|/C(q+1,3) = 3 group elements g that map a triple of X onto
// {inf,0,1} (one list per unordered triple).  This set of g's is the same for every point of the orbit, so the form
// is an orbit invariant; the number of (triple, g) with g(X) = canon(X) equals |Stab(X)|.
// Check: sum of orbit sizes at level t = C(n,t).
// Usage: node orbits_psl2.js q tmax outfile.json   (points 0..q-1 = F_q, q = infinity)
"use strict";
const fs = require("fs");
const q = +process.argv[2], tmax = +process.argv[3], out = process.argv[4];
const n = q + 1, INF = q;
if (n > 32) throw new Error("n <= 32");
const inv = new Array(q).fill(0); for (let a = 1; a < q; a++) for (let b = 1; b < q; b++) if ((a * b) % q === 1) inv[a] = b;
const mob = (a, b, c, d) => { const p = new Int32Array(n); for (let z = 0; z < n; z++) { if (z === INF) p[z] = c === 0 ? INF : (a * inv[c]) % q; else { const num = (a * z + b) % q, den = (c * z + d) % q; p[z] = den === 0 ? INF : (num * inv[den]) % q; } } return p; };
// generators: z+1, s z (s = a nonzero square generating the squares), -1/z
let prim = 2; for (; prim < q; prim++) { const seen = new Set(); let x = 1; for (let i = 0; i < q - 1; i++) { seen.add(x); x = (x * prim) % q; } if (seen.size === q - 1) break; }
const s2 = (prim * prim) % q;
const gens = [mob(1, 1, 0, 1), mob(s2, 0, 0, 1), mob(0, q - 1, 1, 0)];
const key = p => p.join(",");
const G = [new Int32Array([...Array(n).keys()])]; const seenG = new Set([key(G[0])]);
for (let i = 0; i < G.length; i++) for (const h of gens) { const gh = new Int32Array(n); for (let x = 0; x < n; x++) gh[x] = h[G[i][x]]; const k = key(gh); if (!seenG.has(k)) { seenG.add(k); G.push(gh); } }
const order = q * (q * q - 1) / 2;
if (G.length !== order) throw new Error(`group order ${G.length} != ${order}`);
console.error(`PSL(2,${q}) order ${G.length}`);
const bit = x => 2 ** x;
const img = (X, g) => { let r = 0; for (let x = 0; x < n; x++) if (Math.floor(X / bit(x)) % 2 === 1) r += bit(g[x]); return r; };
// per triple: the group elements mapping it onto {INF,0,1}
const tripKey = (a, b, c) => { const t = [a, b, c].sort((u, v) => u - v); return (t[0] * n + t[1]) * n + t[2]; };
const tlist = new Map();
for (const g of G) { const pre = []; for (let x = 0; x < n; x++) if (g[x] === INF || g[x] === 0 || g[x] === 1) pre.push(x); const k = tripKey(...pre); if (!tlist.has(k)) tlist.set(k, []); tlist.get(k).push(g); }
for (const [k, v] of tlist) if (v.length !== order / (n * (n - 1) * (n - 2) / 6)) throw new Error("not 3-homogeneous");
// fast image with point list
function canon(pts) { // pts: array of points (|X| >= 3); returns [canonical mask, stabiliser order]
  let best = Infinity, stab = 0; const L = pts.length;
  for (let i = 0; i < L; i++) for (let j = i + 1; j < L; j++) for (let k = j + 1; k < L; k++) {
    for (const g of tlist.get(tripKey(pts[i], pts[j], pts[k]))) {
      let r = 0; for (let u = 0; u < L; u++) r += bit(g[pts[u]]);
      if (r < best) { best = r; stab = 1; } else if (r === best) stab++;
    }
  }
  return [best, stab];
}
const ptsOf = X => { const p = []; for (let x = 0; x < n; x++) if (Math.floor(X / bit(x)) % 2 === 1) p.push(x); return p; };
const binom = (a, b) => { let r = 1; for (let i = 0; i < b; i++) r = r * (a - i) / (i + 1); return Math.round(r); };
// levels 0..2 by direct reasoning would need canon for |X| < 3; G is 3-homogeneous so levels 1,2,3 have one orbit each.
const levels = []; const t0 = Date.now();
levels[3] = { reps: [canon([0, 1, INF])[0]], size: [binom(n, 3)], edges: null };
for (let t = 3; t < tmax; t++) {
  const L = levels[t]; const idx = new Map(); const reps = [], size = [], edges = [];
  for (let r = 0; r < L.reps.length; r++) {
    const R = L.reps[r]; const P = ptsOf(R); const ch = new Set();
    for (let p = 0; p < n; p++) {
      if (P.includes(p)) continue;
      const [cm, st] = canon([...P, p].sort((a, b) => a - b));
      let id = idx.get(cm);
      if (id === undefined) { id = reps.length; idx.set(cm, id); reps.push(cm); size.push(order / st); }
      ch.add(id);
    }
    edges.push([...ch]);
  }
  L.edges = edges;
  const tot = size.reduce((a, b) => a + b, 0);
  if (tot !== binom(n, t + 1)) throw new Error(`level ${t + 1}: orbit sizes sum ${tot} != C(${n},${t + 1})`);
  levels[t + 1] = { reps, size, edges: null };
  console.error(`level ${t + 1}: ${reps.length} orbits (sizes sum ${tot} = C(${n},${t + 1}) ok) ${(Date.now() - t0) / 1000}s`);
}
fs.writeFileSync(out, JSON.stringify({ q, n, order, gens: gens.map(g => Array.from(g)), levels: levels.map(L => L ? { reps: L.reps, size: L.size, edges: L.edges } : null) }));
console.log(`wrote ${out}`);
