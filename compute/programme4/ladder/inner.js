// Exact DFS for a good seven: at most m members (c-sets, bitmasks on n <= 31 points) covering every pair of [n].
// Input JSON file: {n, m, fam: [masks], oid: [orbit id per member], reps: [indices into fam], nodeLimit}
// The first block ranges over reps (valid for a G-invariant family: any good seven maps to one containing a rep);
// after rep r is exhausted, r's whole orbit is dead (no good seven contains any of its members).
// Branching: the point x with the most uncovered partners, its uncovered partner y with the fewest live candidates,
// candidates = live members containing x and y.  Bounds: for every point ceil(u_x/(c-1)) <= left, and
// sum_x ceil(u_x/(c-1)) <= left*c (each remaining block passes through c points).
// Output JSON: {status: "found"|"none"|"limit", seven: [masks], nodes}
"use strict";
const fs = require("fs");
const inp = JSON.parse(fs.readFileSync(process.argv[2], "utf8"));
const { n, m } = inp; const fam = inp.fam.map(Number); const oid = inp.oid; const reps = inp.reps;
const nodeLimit = inp.nodeLimit || 1e9;
let seed = inp.seed || 0; const rnd = () => { seed = (seed * 1103515245 + 12345) % 2147483648; return seed / 2147483648; };
if (inp.seed) { for (let i = reps.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [reps[i], reps[j]] = [reps[j], reps[i]]; } }
const c = (() => { let x = fam[0], r = 0; while (x) { x &= x - 1; r++; } return r; })();
const FULL = (2 ** n - 1);
const pid = (a, b) => a * n + b;
const byPair = new Array(n * n); for (let i = 0; i < n * n; i++) byPair[i] = [];
for (let j = 0; j < fam.length; j++) {
  const B = fam[j]; const pts = []; for (let x = 0; x < n; x++) if ((B >>> x) & 1) pts.push(x);
  for (let a = 0; a < pts.length; a++) for (let b = a + 1; b < pts.length; b++) { byPair[pid(pts[a], pts[b])].push(j); byPair[pid(pts[b], pts[a])].push(j); }
}
const ptsOf = fam.map(B => { const p = []; for (let x = 0; x < n; x++) if ((B >>> x) & 1) p.push(x); return p; });
const dead = new Uint8Array(Math.max(...oid) + 1);
let cov = new Array(n).fill(0).map((_, x) => (1 << x) >>> 0); // covered partner masks (self counted)
let nodes = 0; const sol = [];
const pc = x => { x = x >>> 0; let r = 0; while (x) { x &= x - 1; r++; } return r; };
function rec(left) {
  if (++nodes > nodeLimit) throw "limit";
  let best = -1, bu = -1, tot = 0;
  for (let x = 0; x < n; x++) {
    const u = pc(~cov[x] & FULL); if (u === 0) continue;
    const need = Math.ceil(u / (c - 1)); if (need > left) return false; tot += need;
    if (u > bu) { bu = u; best = x; }
  }
  if (best < 0) return true;
  if (tot > left * c) return false;
  const x = best; let um = (~cov[x] & FULL) >>> 0;
  let by = -1, bl = 1e18, bc = null;
  while (um) {
    const y = 31 - Math.clz32(um & -um); um &= um - 1;
    const L = byPair[pid(x, y)]; let cnt = 0; for (const j of L) if (!dead[oid[j]]) cnt++;
    if (cnt < bl) { bl = cnt; by = y; if (cnt === 0) return false; }
  }
  const cands = byPair[pid(x, by)].filter(j => !dead[oid[j]]);
  // order by number of newly covered (ordered) pairs, descending
  const score = j => { let s = 0; for (const p of ptsOf[j]) s += pc(fam[j] & ~cov[p] & FULL); return s; };
  const sc = cands.map(j => [score(j) + (inp.seed ? rnd() * 3 : 0), j]).sort((a, b) => b[0] - a[0]);
  for (const [, j] of sc) {
    const saved = cov.slice(); const B = fam[j];
    for (const p of ptsOf[j]) cov[p] = (cov[p] | B) >>> 0;
    sol.push(B);
    if (rec(left - 1)) return true;
    sol.pop(); cov = saved;
  }
  return false;
}
let status = "none", seven = null;
try {
  for (const r of reps) {
    const B = fam[r]; const saved = cov.slice();
    for (const p of ptsOf[r]) cov[p] = (cov[p] | B) >>> 0;
    sol.push(B);
    if (rec(m - 1)) { status = "found"; seven = sol.slice(); break; }
    sol.pop(); cov = saved; dead[oid[r]] = 1;
  }
} catch (e) { if (e === "limit") status = "limit"; else throw e; }
console.log(JSON.stringify({ status, seven, nodes }));
