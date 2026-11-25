// CORE 55.5, decisive method: exhaustive search over co-type assignments.
// A good seven K_0..K_6 (members, size c, on n points) gives every point x a co-type I_x = {i : x in K_i} with
// (a) I_x pairwise intersecting (all pairs covered, x = y included), (b) |{x : i in I_x}| = c for every i,
// (c) |I_x| >= 3 when 2(c-1) < n-1 (a point in two members sees at most 2(c-1) others), and then
//     sum_x (|I_x| - 3) = 7c - 3n.  Conversely any such assignment with all K_i members is a good seven.
// Search: points in order 0..n-1; I_x ranges over subsets of [7] meeting all previous co-types; the 7 labels are
// interchangeable, so the columns K_0..K_6 are required to be lexicographically non-increasing (read from point 0):
// while columns i, i+1 agree on the prefix, i+1 in I_x forces i in I_x (lex-leader symmetry breaking, sound);
// prune: degree of each label <= c, excess budget, and every partial K_i must agree on points 0..x with some member
// (prefix table).  Exhaustive: prints every good seven found (or stops at the first if STOP=1).
// Usage: node seven_cotype.js famfile n [all]
const fs = require('fs');
const [file, nS, allS] = process.argv.slice(2); const n = +nS; const ALL = allS === 'all';
const fam = fs.readFileSync(file, 'utf8').trim().split(/\n/).map(l => l.trim().split(/\s+/).reduce((m, x) => m | (1 << +x), 0));
const popc = m => { let s = 0; while (m) { m &= m - 1; s++; } return s; };
const c = popc(fam[0]); if (!fam.every(m => popc(m) === c)) throw 'non-uniform';
const need3 = 2 * (c - 1) < n - 1; const minSize = need3 ? 3 : 1; const budget = need3 ? 7 * c - 3 * n : Infinity;
// prefix tables: pref[x][mask restricted to points 0..x] = 1 if some member restricts to it
const pref = []; for (let x = 0; x < n; x++) { const t = new Uint8Array(1 << (x + 1)); const pm = (1 << (x + 1)) - 1; for (const m of fam) t[m & pm] = 1; pref.push(t); }
const subsets = []; for (let s = 1; s < 128; s++) if (popc(s) >= minSize) subsets.push(s); subsets.sort((a, b) => popc(a) - popc(b) || a - b);
const I = new Array(n).fill(0), K = new Array(7).fill(0), deg = new Array(7).fill(0);
let nodes = 0, sols = 0, first = null;
function rec(x, tied, exc) {
  nodes++;
  if (x === n) {
    for (let i = 0; i < 7; i++) if (!pref[n - 1][K[i]]) return false;
    sols++; if (!first) first = K.slice(); return !ALL;
  }
  const rem = n - 1 - x;
  for (const s of subsets) {
    const e = popc(s) - minSize; if (exc + e > budget) continue;
    let ok = true;
    for (let i = 0; i < 6; i++) if ((tied >> i & 1) && (s >> (i + 1) & 1) && !(s >> i & 1)) { ok = false; break; } if (!ok) continue;
    for (let y = 0; y < x; y++) if (!(I[y] & s)) { ok = false; break; } if (!ok) continue;
    for (let i = 0; i < 7; i++) { const d = deg[i] + (s >> i & 1); if (d > c || d + rem < c) { ok = false; break; } } if (!ok) continue;
    for (let i = 0; i < 7; i++) if (s >> i & 1) { K[i] |= 1 << x; deg[i]++; }
    I[x] = s;
    let ext = true; for (let i = 0; i < 7; i++) if (!pref[x][K[i]]) { ext = false; break; }
    if (ext) {
      let nt = 0; for (let i = 0; i < 6; i++) if ((tied >> i & 1) && ((s >> i & 1) === (s >> (i + 1) & 1))) nt |= 1 << i;
      if (rec(x + 1, nt, exc + e)) return true;
    }
    for (let i = 0; i < 7; i++) if (s >> i & 1) { K[i] &= ~(1 << x); deg[i]--; }
  }
  I[x] = 0; return false;
}
const t0 = Date.now(); rec(0, 63, 0);
const show = m => '{' + [...Array(n).keys()].filter(y => m >> y & 1).join(',') + '}';
if (first) {
  const set = new Set(fam); const cov = first.every(m => set.has(m));
  let allPairs = true; for (let a = 0; a < n; a++) for (let b = a; b < n; b++) if (!first.some(m => (m >> a & 1) && (m >> b & 1))) allPairs = false;
  console.log(`GOOD SEVEN FOUND: ${first.map(show).join(' ')}; members: ${cov}; all pairs: ${allPairs}; sols counted ${sols}; nodes ${nodes}; ${(Date.now()-t0)/1000}s`);
} else console.log(`NO good seven [exact, exhaustive co-type search]: nodes ${nodes}; ${(Date.now()-t0)/1000}s`);
