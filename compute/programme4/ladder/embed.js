// Second, solver-free method for the inner check: for each isomorphism class of pair-covering (configuration =
// multiset of co-types, from cotypes2.js), exhaustively search for an assignment of the n points to co-types
// (co-type T used exactly mult(T) times) such that every block B_i = {x : i in co-type(x)} is a member of F.
// Pruning: after assigning points p_0..p_j (in the given order), every block's trace on those points must be the
// trace of some member of F (prefix tables, exact).  No symmetry breaking (complete by construction).
// Usage: node embed.js famfile n configfile [first last] [order comma list]
// Prints per class: NONE (exhausted, nodes) or FOUND blocks.
"use strict";
const fs = require("fs");
const [famfile, nS, cfgfile, aS, bS, ordS] = process.argv.slice(2);
const n = +nS;
const fam = fs.readFileSync(famfile, "utf8").split(/\r?\n/).filter(l => l.trim()).map(l => l.trim().split(/\s+/).map(Number));
const order = ordS ? ordS.split(",").map(Number) : [...Array(n).keys()];
if (new Set(order).size !== n) throw new Error("order must be a permutation");
const pos = new Array(n); order.forEach((x, j) => pos[x] = j);
const famM = fam.map(B => B.reduce((s, x) => s | (1 << pos[x]), 0) >>> 0);
const famSet = new Set(fam.map(B => B.slice().sort((a, b) => a - b).join(",")));
const pref = []; for (let j = 0; j <= n; j++) { const msk = (2 ** j - 1); const S = new Set(); for (const B of famM) S.add((B & msk) >>> 0); pref.push(S); }
const cfgs = fs.readFileSync(cfgfile, "utf8").split(/\r?\n/).filter(l => l.trim()).map(l => l.split("|")[0].trim().split(/\s+/).map(t => t.split(":").map(Number)));
const a = aS ? +aS : 0, b = bS ? +bS : cfgs.length;
const m = 7;
let total = 0;
for (let ci = a; ci < b; ci++) {
  const types = cfgs[ci].map(t => t[0]); const mult = cfgs[ci].map(t => t[1]);
  if (mult.reduce((s, v) => s + v, 0) !== n) throw new Error("bad config");
  const col = new Array(m).fill(0); let nodes = 0; let found = null; const t0 = Date.now();
  const rec = (j) => {
    nodes++;
    if (j === n) { found = col.slice(); return true; }
    const P = pref[j + 1], bit = (2 ** j);
    for (let t = 0; t < types.length; t++) {
      if (mult[t] === 0) continue;
      const T = types[t]; let ok = true;
      for (let i = 0; i < m; i++) { const v = (T >> i) & 1 ? (col[i] + bit) : col[i]; if (!P.has(v)) { ok = false; break; } }
      if (!ok) continue;
      mult[t]--; for (let i = 0; i < m; i++) if ((T >> i) & 1) col[i] += bit;
      if (rec(j + 1)) return true;
      mult[t]++; for (let i = 0; i < m; i++) if ((T >> i) & 1) col[i] -= bit;
    }
    return false;
  };
  const r = rec(0); total += nodes;
  if (r) {
    const blocks = found.map(B => order.filter((x, j) => Math.floor(B / 2 ** j) % 2 === 1).sort((x, y) => x - y));
    // plain re-check: members of F, every pair covered
    const okm = blocks.every(B => famSet.has(B.join(",")));
    const cov = new Set(); for (const B of blocks) for (let u = 0; u < B.length; u++) for (let w = u + 1; w < B.length; w++) cov.add(B[u] * n + B[w]);
    console.log(`class ${ci}: FOUND nodes ${nodes} members_ok ${okm} pairs ${cov.size}/${n * (n - 1) / 2} ${JSON.stringify(blocks)}`);
  } else console.log(`class ${ci}: NONE nodes ${nodes} (${(Date.now() - t0) / 1000}s)`);
}
console.log(`total nodes ${total}`);
