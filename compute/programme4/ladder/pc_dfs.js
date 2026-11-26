// Exact DFS: does family F (c-subsets of [n]) contain m members covering every pair of [n]?
// Rows = points 0..n-1 in a given order; each point gets a co-type T subset of [m] (blocks containing it),
// |T| >= rmin = ceil((n-1)/(c-1)) (a point in fewer blocks cannot meet its n-1 partners), co-types pairwise
// intersecting (= every pair covered), sum of (|T| - rmin) <= E = m*c - rmin*n (block sizes), and after row j every
// column restricted to the first j+1 points must be the trace of a member of F (prefix tables), column count <= c.
// Block symmetry: columns kept in non-increasing lex order (column i >= column i+1 as 0/1 vectors read from row 0);
// blocks of a minimum cover are distinct, so this is a valid symmetry breaking for m = minimum.
// Usage: node pc_dfs.js famfile n m [order: comma list of points] ; prints FOUND + blocks, or NONE + node count.
"use strict";
const fs = require("fs");
const [famfile, nS, mS, ordS] = process.argv.slice(2);
const n = +nS, m = +mS;
let fam = fs.readFileSync(famfile, "utf8").split(/\r?\n/).filter(l => l.trim()).map(l => l.trim().split(/\s+/).map(Number));
const c = fam[0].length;
const order = ordS ? ordS.split(",").map(Number) : [...Array(n).keys()];
const pos = new Array(n); order.forEach((x, j) => pos[x] = j);
// re-index points by position in order
const famM = fam.map(B => B.reduce((s, x) => s | (1 << pos[x]), 0) >>> 0);
const rmin = Math.ceil((n - 1) / (c - 1)), E = m * c - rmin * n;
const pref = [];
for (let j = 0; j <= n; j++) { const msk = j === 32 ? 0xffffffff : ((1 << j) - 1) >>> 0; const S = new Set(); for (const B of famM) S.add((B & msk) >>> 0); pref.push(S); }
const pc = x => { let r = 0; while (x) { x &= x - 1; r++; } return r; };
const types = []; for (let T = 0; T < (1 << m); T++) if (pc(T) >= rmin) types.push(T);
types.sort((a, b) => pc(a) - pc(b) || a - b);
const col = new Array(m).fill(0), cnt = new Array(m).fill(0), rowT = new Array(n).fill(0);
let nodes = 0, found = null; const t0 = Date.now();
function dfs(j, extra) {
  nodes++;
  if ((nodes & 0xfffff) === 0) process.stderr.write(`nodes ${nodes} depth ${j} t ${(Date.now() - t0) / 1000}s\n`);
  if (j === n) { found = col.slice(); return true; }
  const left = n - j - 1, bit = 1 << j;
  for (const T of types) {
    const e = pc(T) - rmin; if (extra + e > E) continue;
    let ok = true;
    for (let p = 0; p < j; p++) if ((rowT[p] & T) === 0) { ok = false; break; }
    if (!ok) continue;
    // column counts and lex
    for (let i = 0; i < m && ok; i++) {
      const inT = (T >> i) & 1;
      const nc = cnt[i] + inT; if (nc > c || nc + left < c) ok = false;
      if (ok && i + 1 < m && col[i] === col[i + 1] && !inT && ((T >> (i + 1)) & 1)) ok = false;
    }
    if (!ok) continue;
    const P = pref[j + 1];
    for (let i = 0; i < m && ok; i++) { const v = ((T >> i) & 1) ? (col[i] | bit) >>> 0 : col[i]; if (!P.has(v)) ok = false; }
    if (!ok) continue;
    for (let i = 0; i < m; i++) if ((T >> i) & 1) { col[i] = (col[i] | bit) >>> 0; cnt[i]++; }
    rowT[j] = T;
    if (dfs(j + 1, extra + e)) return true;
    for (let i = 0; i < m; i++) if ((T >> i) & 1) { col[i] = (col[i] & ~bit) >>> 0; cnt[i]--; }
  }
  return false;
}
const res = dfs(0, 0);
const sec = (Date.now() - t0) / 1000;
if (res) {
  const blocks = found.map(B => order.filter((x, j) => (B >> j) & 1).sort((a, b) => a - b));
  console.log(`FOUND nodes ${nodes} ${sec}s blocks ${JSON.stringify(blocks)}`);
} else console.log(`NONE nodes ${nodes} ${sec}s (n=${n} m=${m} c=${c} rmin=${rmin} E=${E} |F|=${fam.length})`);
