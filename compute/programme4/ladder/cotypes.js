// All co-type configurations of a pair-covering of [n] by m blocks of size c, up to S_m (block relabelling).
// Configuration = multiset of n subsets of [m] (co-types I_x = blocks containing x), pairwise intersecting (every pair
// of points covered), each of size >= rmin = ceil((n-1)/(c-1)), every label in exactly c of them (|B_i| = c).
// Pair-coverings by m c-sets up to S_n x S_m  <->  configurations up to S_m.
// DFS: co-types chosen in non-decreasing mask order (multiset); WLOG the first is {0..rmin-1} (needs E < n, so some
// point has exactly rmin blocks; relabel the blocks).  Prunes: compatibility with all chosen, label degree <= c,
// extra <= E, and every label's remaining need is coverable by compatible later masks.
// Dedup: orbit marking -- each new labelled leaf's whole S_m-orbit is inserted into a visited set; class count exact.
// Usage: node cotypes.js n m c outfile
"use strict";
const fs = require("fs");
const [n, m, c] = process.argv.slice(2, 5).map(Number); const out = process.argv[5];
const pc = x => { let r = 0; while (x) { x &= x - 1; r++; } return r; };
const rmin = Math.ceil((n - 1) / (c - 1)), E = m * c - rmin * n;
if (!(E >= 0 && E < n)) throw "E";
const masks = []; for (let s = 0; s < (1 << m); s++) if (pc(s) >= rmin) masks.push(s);
masks.sort((a, b) => pc(a) - pc(b) || a - b);
const M = masks.length;
function* permsGen(a) { if (a.length <= 1) { yield a; return; } for (let i = 0; i < a.length; i++) for (const p of permsGen([...a.slice(0, i), ...a.slice(i + 1)])) yield [a[i], ...p]; }
const perms = [...permsGen([...Array(m).keys()])];
const ptab = perms.map(p => { const t = new Int32Array(1 << m); for (let s = 0; s < (1 << m); s++) { let v = 0; for (let i = 0; i < m; i++) if (s >> i & 1) v |= 1 << p[i]; t[s] = v; } return t; });
const key = arr => arr.join(",");
const visited = new Set(); const classes = []; let leaves = 0, nodes = 0; const t0 = Date.now();
const cur = []; const deg = new Array(m).fill(0);
function leaf() {
  leaves++;
  const k = key(cur.slice().sort((a, b) => a - b)); if (visited.has(k)) return;
  let best = null, aut = 0;
  for (const t of ptab) {
    const im = cur.map(s => t[s]).sort((a, b) => a - b); const ik = key(im);
    if (ik === k) aut++;
    visited.add(ik);
    if (best === null || ik < best) best = ik;
  }
  classes.push([best, aut]);
}
function dfs(j, cnt, extra) {
  nodes++;
  if (cnt === n) { if (extra === E) leaf(); return; }
  const rem = n - cnt;
  for (let i = 0; i < m; i++) if (c - deg[i] > rem) return;
  for (let q = j; q < M; q++) {
    const s = masks[q], e = pc(s) - rmin;
    if (extra + e > E) continue;
    let ok = true; for (const u of cur) if ((s & u) === 0) { ok = false; break; }
    if (!ok) continue;
    for (let i = 0; i < m; i++) if (s >> i & 1 && deg[i] + 1 > c) { ok = false; break; }
    if (!ok) continue;
    for (let i = 0; i < m; i++) if (s >> i & 1) deg[i]++;
    cur.push(s);
    // future feasibility: each label with need > 0 must lie in some mask q' >= q compatible with all chosen
    let feas = true; const left = rem - 1;
    if (left > 0) {
      let cov = 0;
      for (let q2 = q; q2 < M; q2++) { const s2 = masks[q2]; if (pc(s2) - rmin + extra + e > E) continue; let ok2 = true; for (const u of cur) if ((s2 & u) === 0) { ok2 = false; break; } if (ok2) cov |= s2; }
      for (let i = 0; i < m; i++) if (deg[i] < c && !(cov >> i & 1)) { feas = false; break; }
    } else for (let i = 0; i < m; i++) if (deg[i] !== c) feas = false;
    if (feas) dfs(q, cnt + 1, extra + e);
    cur.pop(); for (let i = 0; i < m; i++) if (s >> i & 1) deg[i]--;
    if (cnt === 0) break; // first co-type is masks[0] = {0..rmin-1} WLOG
  }
}
dfs(0, 0, 0);
classes.sort((a, b) => a[0] < b[0] ? -1 : 1);
fs.writeFileSync(out, classes.map(([k, a]) => `${k} aut_m=${a}`).join("\n") + "\n");
console.log(`n=${n} m=${m} c=${c} rmin=${rmin} E=${E}: nodes ${nodes}, labelled leaves (with first co-type fixed) ${leaves}, classes up to S_${m}: ${classes.length} (${(Date.now() - t0) / 1000}s) -> ${out}`);
