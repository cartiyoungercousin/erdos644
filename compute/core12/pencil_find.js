// CORE 113: exhaustive search for (Sigma)(b) pencils in an explicit co-edge family (members as bitmasks, n <= 31).
// Pencil = three members with union V and triple intersection >= kap0 := n - 2T.  [computed exact when run to the end]
// Count (hand): 3c = n + 2*kappa + d2 (d_j = #points in exactly j members, d0 = 0), so for kappa >= kap0 the pair overlap
// o = |K1 ∩ K2| satisfies kap0 <= o <= kap0 + d2max; and K3 ⊇ V \ (K1 ∪ K2). We enumerate every member K1, every K2 = A ∪ B
// with A ⊆ K1 (|A| = o), B ⊆ V \ K1, look K2 up, and then test every candidate K3 ⊇ V∖(K1∪K2) of size c that is a member,
// by enumerating K3 ∖ (V∖(K1∪K2)) ⊆ K1 ∪ K2 (generic, no case split) and checking the triple intersection.
// Usage: node pencil_find.js famfile n k T maxout   -> prints "P a b c" (masks) lines, then "DONE count exhaustive|truncated"
const fs = require('fs');
const [file, nS, kS, TS, moS] = process.argv.slice(2); const n = +nS, k = +kS, T = +TS, maxout = +moS;
const c = n - k, kap0 = n - 2 * T, FULL = (2 ** n) - 1;
const fam = fs.readFileSync(file, 'utf8').trim().split(/\s+/).map(Number);
const isMem = new Uint8Array(2 ** n); for (const m of fam) isMem[m] = 1;
const pc = m => { let s = 0; while (m) { m &= m - 1; s++; } return s; };
const bits = m => { const r = []; for (let i = 0; i < n; i++) if (m >> i & 1) r.push(1 << i); return r; };
function* subsets(arr, r, start = 0, acc = 0) { if (r === 0) { yield acc; return; } for (let i = start; i <= arr.length - r; i++) yield* subsets(arr, r - 1, i + 1, acc | arr[i]); }
// overlap range: d2 <= 3c - n - 2*kap0
const d2max = 3 * c - n - 2 * kap0; let found = 0; const out = [];
if (d2max < 0) { console.log('DONE 0 exhaustive (count excludes pencils)'); process.exit(0); }
const seen = new Set();
// iterate K1 in a pseudo-random order (seeded) so that truncated outputs spread over the family
let sd = 12345; const ord = fam.slice(); for (let i = ord.length - 1; i > 0; i--) { sd = (sd * 1103515245 + 12345) & 0x7fffffff; const j = sd % (i + 1); [ord[i], ord[j]] = [ord[j], ord[i]]; }
outer:
for (const K1 of ord) {
  const in1 = bits(K1), out1 = bits(FULL & ~K1);
  for (let o = kap0; o <= Math.min(c, kap0 + d2max); o++) {
    if (c - o > out1.length) continue;
    for (const A of subsets(in1, o)) for (const B of subsets(out1, c - o)) {
      const K2 = A | B; if (!isMem[K2] || K2 <= K1) continue;
      const U = K1 | K2, R = FULL & ~U, need = c - pc(R); if (need < 0) continue;
      // K3 = R ∪ Y ∪ Z with Y ⊆ K1∩K2 (|Y| >= kap0, needed for the triple intersection), Z ⊆ K1 Δ K2
      const I12 = bits(K1 & K2), D12 = bits(K1 ^ K2);
      for (let y = Math.max(kap0, need - D12.length); y <= Math.min(need, I12.length); y++)
        for (const Y of subsets(I12, y)) for (const Z of subsets(D12, need - y)) {
          const K3 = R | Y | Z; if (!isMem[K3] || K3 <= K2) continue;   // K1 < K2 < K3 avoids repeats
          out.push(`P ${K1} ${K2} ${K3}`); found++; if (found >= maxout) break outer;
        }
    }
  }
}
// note: K1 < K2 < K3 ordering is complete: every pencil {K1,K2,K3} is found with K1 its smallest member.
console.log(out.join('\n')); console.log(`DONE ${found} ${found >= maxout ? 'truncated' : 'exhaustive'}`);
