// Pair-coverings of [n] by m = 7 blocks of size c with rmin = ceil((n-1)/(c-1)) = 3, up to isomorphism, via co-types.
// A covering <-> multiset of n co-types (subsets of [7]), pairwise intersecting, sizes >= 3, each label in exactly c.
// E = 7c - 3n = sum(|I_x| - 3).  Large co-types (size >= 4) have sizes 3 + parts of a partition of E; the n - #parts
// triples form a multiset whose SUPPORT S (distinct triples) is an intersecting family.  Two configurations with the same
// canonical support are isomorphic iff related by Aut(S), so dedup is done under Aut(S) only.
// Steps: (1) supports up to S_7 (orderly BFS, canonical = min image over 5040 perms); (2) for each support and each
// partition: large co-types (multiset, each meeting every triple of S; two sets of size >= 4 in [7] always meet),
// then triple multiplicities mu_T >= 1 with exact label degrees; (3) canonicalise under Aut(S).
// Usage: node cotypes2.js n c outfile      Output lines: "mask:mult ... | aut=<|Aut| in S_7 of the multiset>"
"use strict";
const fs = require("fs");
const [n, c] = process.argv.slice(2, 4).map(Number); const out = process.argv[4];
const m = 7; const pc = x => { let r = 0; while (x) { x &= x - 1; r++; } return r; };
const rmin = Math.ceil((n - 1) / (c - 1)), E = m * c - rmin * n;
if (rmin !== 3 || E < 0 || E >= n) throw new Error(`need rmin=3, 0<=E<n (rmin ${rmin}, E ${E})`);
const t0 = Date.now();
function* permsGen(a) { if (a.length <= 1) { yield a; return; } for (let i = 0; i < a.length; i++) for (const p of permsGen([...a.slice(0, i), ...a.slice(i + 1)])) yield [a[i], ...p]; }
const perms = [...permsGen([...Array(m).keys()])];
const ptab = perms.map(p => { const t = new Int32Array(128); for (let s = 0; s < 128; s++) { let v = 0; for (let i = 0; i < m; i++) if (s >> i & 1) v |= 1 << p[i]; t[s] = v; } return t; });
const triples = []; for (let s = 0; s < 128; s++) if (pc(s) === 3) triples.push(s);
const cmpArr = (a, b) => { for (let i = 0; i < Math.min(a.length, b.length); i++) if (a[i] !== b[i]) return a[i] - b[i]; return a.length - b.length; };
function canonSet(S) { let best = null; for (const t of ptab) { const im = S.map(s => t[s]).sort((a, b) => a - b); if (!best || cmpArr(im, best) < 0) best = im; } return best; }
// (1) supports
let level = [[]]; const supports = [];
while (level.length) {
  const nxt = new Map();
  for (const S of level) {
    supports.push(S);
    for (const t of triples) {
      if (S.includes(t) || S.some(u => (u & t) === 0)) continue;
      const cs = canonSet([...S, t]); nxt.set(cs.join(","), cs);
    }
  }
  level = [...nxt.values()];
}
console.error(`supports (intersecting triple families up to S_7, incl. empty): ${supports.length} (${(Date.now() - t0) / 1000}s)`);
// partitions of E
function* partitions(x, maxp) { if (x === 0) { yield []; return; } for (let p = Math.min(x, maxp); p >= 1; p--) for (const r of partitions(x - p, p)) yield [p, ...r]; }
const parts = [...partitions(E, E)].filter(p => p.every(q => 3 + q <= m));
const results = []; let labelledTotal = 0n;
const fact = k => { let r = 1n; for (let i = 2n; i <= BigInt(k); i++) r *= i; return r; };
for (const S of supports) {
  if (S.length === 0) continue;
  const aut = ptab.filter(t => { const im = S.map(s => t[s]).sort((a, b) => a - b); return cmpArr(im, S) === 0; });
  const found = new Set();
  for (const part of parts) {
    const t3 = n - part.length; if (S.length > t3) continue;
    // large co-type candidates by size
    const sizes = part.map(p => 3 + p);
    const cand = {}; for (const sz of new Set(sizes)) { cand[sz] = []; for (let s = 0; s < 128; s++) if (pc(s) === sz && S.every(T => (T & s) !== 0)) cand[sz].push(s); }
    // choose multiset of large co-types: sizes sorted desc (part is non-increasing), same size -> non-decreasing mask index
    const L = [];
    const chooseLarge = (i, minIdx) => {
      if (i === sizes.length) { solveTriples(L.slice()); return; }
      const sz = sizes[i]; const start = (i > 0 && sizes[i - 1] === sz) ? minIdx : 0;
      for (let q = start; q < cand[sz].length; q++) { L.push(cand[sz][q]); chooseLarge(i + 1, q); L.pop(); }
    };
    const solveTriples = (Lg) => {
      const d = new Array(m).fill(c); for (const s of Lg) for (let i = 0; i < m; i++) if (s >> i & 1) d[i]--;
      if (d.some(v => v < 0)) return;
      // mu_T >= 1, sum_{T ni i} mu_T = d_i
      const base = d.slice(); for (const T of S) for (let i = 0; i < m; i++) if (T >> i & 1) base[i]--;
      if (base.some(v => v < 0)) return;
      const extra = new Array(S.length).fill(0); // mu - 1
      const rec = (k) => {
        if (k === S.length) {
          if (base.some(v => v !== 0)) return;
          const cfg = []; S.forEach((T, j) => { for (let q = 0; q <= extra[j]; q++) cfg.push(T); }); cfg.push(...Lg);
          if (cfg.length !== n) throw new Error("count");
          // canonical under Aut(S)
          let best = null; for (const t of aut) { const im = cfg.map(s => t[s]).sort((a, b) => a - b); if (!best || cmpArr(im, best) < 0) best = im; }
          found.add(best.join(","));
          return;
        }
        const T = S[k]; const lab = []; for (let i = 0; i < m; i++) if (T >> i & 1) lab.push(i);
        // labels whose last triple is T must be completed here
        let maxe = Math.min(...lab.map(i => base[i]));
        for (let e = 0; e <= maxe; e++) {
          for (const i of lab) base[i] -= e; extra[k] = e;
          // prune: any label with base>0 must lie in a later triple
          let ok = true; for (let i = 0; i < m && ok; i++) if (base[i] > 0) { let f = false; for (let k2 = k + 1; k2 < S.length; k2++) if (S[k2] >> i & 1) { f = true; break; } if (!f) ok = false; }
          if (ok) rec(k + 1);
          for (const i of lab) base[i] += e;
        }
        extra[k] = 0;
      };
      rec(0);
    };
    chooseLarge(0, 0);
  }
  for (const k of found) {
    const cfg = k.split(",").map(Number);
    const a = ptab.filter(t => cmpArr(cfg.map(s => t[s]).sort((x, y) => x - y), cfg) === 0).length;
    const mult = new Map(); for (const s of cfg) mult.set(s, (mult.get(s) || 0) + 1);
    let pm = 1n; for (const v of mult.values()) pm *= fact(v);
    const lab = fact(n) / (BigInt(a) * pm); labelledTotal += lab;
    results.push(`${[...mult.entries()].map(([s, v]) => `${s}:${v}`).join(" ")} | aut=${a} labelled=${lab}`);
  }
}
fs.writeFileSync(out, results.join("\n") + "\n");
console.log(`n=${n} c=${c} E=${E}: ${results.length} pair-coverings by 7 blocks up to isomorphism; labelled (as block sets on [n]) ${labelledTotal}; ${(Date.now() - t0) / 1000}s -> ${out}`);
