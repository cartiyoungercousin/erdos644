// CORE 55.5, third independent method: exhaustive search for seven members covering all pairs of V (n <= 31, members as bitmasks).
// Argument [proved by hand]: in a pair-cover by seven c-sets with 3(c-1) >= n-1 > 2(c-1), every point has r_x >= 3 and
// sum_x (r_x - 3) = 7c - 3n, so at most 7c - 3n points have r_x > 3; among any 7c - 3n + 1 points some x has r_x = 3 exactly:
// three chosen members contain x and their union is V, and the other four avoid x.  We enumerate, for each x in {0..7c-3n},
// every such triple and complete it by a depth-4 DFS over members avoiding x.  Exhaustive: prints every good seven found (stops at first).
// Usage: node seven_dfs.js famfile n
const fs = require('fs');
const [file, nS] = process.argv.slice(2); const n = +nS; const FULL = (1 << n) - 1;
const fam = fs.readFileSync(file, 'utf8').trim().split(/\n/).map(l => l.trim().split(/\s+/).reduce((m, x) => m | (1 << +x), 0));
const c = popc(fam[0]); const slack = 7 * c - 3 * n;
function popc(m) { let s = 0; while (m) { m &= m - 1; s++; } return s; }
if (!(3 * (c - 1) >= n - 1 && 2 * (c - 1) < n - 1)) throw new Error('r_x >= 3 argument needs 2(c-1) < n-1 <= 3(c-1)');
const isMem = new Uint8Array(1 << n); for (const m of fam) isMem[m] = 1;
const maxPairs = c * (c - 1) / 2;
let triples = 0, nodes = 0, found = null;
function uncovered(cov) { let u = 0; for (let y = 0; y < n; y++) u += popc(FULL & ~cov[y] & ~((1 << (y + 1)) - 1)); return u; }
function dfs(cov, r, rem, cand, chosen) {
  nodes++;
  // excess pruning: sum_y (r_y - 3)^+ <= slack at every stage; deficiency: sum_y (3 - r_y)^+ <= c * rem
  let exc = 0, def = 0; for (let y = 0; y < n; y++) { if (r[y] > 3) exc += r[y] - 3; else def += 3 - r[y]; }
  if (exc > slack || def > c * rem) return false;
  let best = null, bestCnt = 1e9, any = false;
  for (let y = 0; y < n; y++) {
    let miss = FULL & ~cov[y] & ~((1 << (y + 1)) - 1);
    while (miss) {
      const z = 31 - Math.clz32(miss & -miss); miss &= miss - 1; any = true;
      if (rem === 0) return false;
      const need = (1 << y) | (1 << z); let cnt = 0;
      for (const m of cand) if ((m & need) === need) cnt++;
      if (cnt < bestCnt) { bestCnt = cnt; best = need; if (cnt === 0) return false; }
    }
  }
  if (!any) { found = chosen.slice(); return true; }
  if (uncovered(cov) > rem * maxPairs) return false;
  for (const m of cand) {
    if ((m & best) !== best) continue;
    const nc = cov.slice(), nr = r.slice(); for (let y = 0; y < n; y++) if (m >> y & 1) { nc[y] |= m; nr[y]++; }
    chosen.push(m); if (dfs(nc, nr, rem - 1, cand, chosen)) return true; chosen.pop();
  }
  return false;
}
for (let x = 0; x <= Math.min(slack, n - 1) && !found; x++) {
  const thr = fam.filter(m => m >> x & 1), avoid = fam.filter(m => !(m >> x & 1));
  for (let i = 0; i < thr.length && !found; i++) for (let j = i + 1; j < thr.length && !found; j++) {
    const A = thr[i], B = thr[j], need = FULL & ~(A | B);
    if (popc(need) > c - 1) continue;
    // every C >= need | x, C a member, C > B (index order): enumerate by scanning thr from j+1
    for (let l = j + 1; l < thr.length; l++) {
      const C = thr[l]; if ((C & need) !== need) continue;
      triples++;
      const cov = new Array(n).fill(0), r = new Array(n).fill(0); for (const m of [A, B, C]) for (let y = 0; y < n; y++) if (m >> y & 1) { cov[y] |= m; r[y]++; }
      if (dfs(cov, r, 4, avoid, [A, B, C])) break;
    }
  }
  console.log(`x=${x}: done; triples so far ${triples}, dfs nodes ${nodes}${found ? ', FOUND' : ''}`);
}
const show = m => '{' + [...Array(n).keys()].filter(y => m >> y & 1).join(',') + '}';
if (found) {
  const cov = new Array(n).fill(0); for (const m of found) { if (!isMem[m]) throw 'not a member'; for (let y = 0; y < n; y++) if (m >> y & 1) cov[y] |= m; }
  console.log('GOOD SEVEN:', found.map(show).join(' '), 'check all pairs:', cov.every(v => v === FULL));
} else console.log(`NO good seven: exhaustive over x in 0..${slack}, ${triples} covering triples, ${nodes} DFS nodes [exact]`);
