"""Generates petal_select.js (C4) and petal.js (C1-C3) from the validated engine in exact7d.js."""
s = open('exact7d.js', encoding='utf-8').read()
cut = s.index("const k = parseInt(process.argv[2]);")
head = s[:cut]
common = r'''
// ---- four-petal confined game (TWIN 15): four fixed replies, three further requests -----------------------
// A configuration is a list of (type mask over the 4 petals, count).  Requester wins iff engine.win(state, 4).
const quadCache = new Map();
let quadCalls = 0, quadTime = 0;
function quadWin(g, masks, counts) {          // masks over 4 petals; only points in covering pairs matter
  const rm = [], rc = [];
  for (let x = 0; x < masks.length; x++) {
    if (!counts[x]) continue;
    const need = 15 & ~masks[x];
    let ok = false;
    for (let y = 0; y < masks.length; y++) if (counts[y] && (masks[y] & need) === need) { ok = true; break; }
    if (ok) { rm.push(masks[x]); rc.push(counts[x]); }
  }
  if (rm.length === 0) return true;
  const code = canon(rm, rc, rm.length, 4);
  const key = code.join(',');
  let r = quadCache.get(key);
  if (r !== undefined) return r;
  const t0 = Date.now();
  r = g.win(code, 4);
  quadCalls++; quadTime += Date.now() - t0;
  quadCache.set(key, r);
  return r;
}
function Lstar(a, b) {
  const c = [a + b / 3, b + a / 3, 2 * (a + b) / 3];
  if (b >= a / 2) c.push(3 * a / 4 + b / 2);
  if (a >= b / 2) c.push(3 * b / 4 + a / 2);
  return Math.min(...c);
}
'''
sel = r'''
// ---- C4: selection game in the open setting.  J replies; she wins iff some four of them are triple-free and
// form a requester-winning four-petal configuration (exact table, evaluated on demand).  m = J + 3 requests.
// usage: node petal_select.js k T Jmax [seconds]
const k = parseInt(process.argv[2]), T = parseInt(process.argv[3]), Jmax = parseInt(process.argv[4]);
const limit = process.argv[5] ? parseFloat(process.argv[5]) : 1100;
const g = new Game(k, T);
const FULL = !!process.env.FULL;      // FULL: any four replies, exact four-petal value (triple points allowed)
function winningQuad(masks, cnt, n, j) {
  for (let a = 0; a < j; a++) for (let b = a + 1; b < j; b++) for (let c = b + 1; c < j; c++) for (let d = c + 1; d < j; d++) {
    const pm = new Map();
    let bad = false;
    for (let x = 0; x < n && !bad; x++) {
      const m = masks[x];
      const v = ((m >> a) & 1) | (((m >> b) & 1) << 1) | (((m >> c) & 1) << 2) | (((m >> d) & 1) << 3);
      const pc = popc(v);
      if (pc === 4 || (pc >= 3 && !FULL)) bad = true;      // a common point of the four petals is never allowed
      else if (pc >= 1) pm.set(v, (pm.get(v) || 0) + cnt[x]);        // singles matter as partners of triple points
    }
    if (bad) continue;
    const mm = [...pm.keys()], cc = mm.map(v => pm.get(v));
    if (quadWin(g, mm, cc)) return [a + 1, b + 1, c + 1, d + 1];
  }
  return null;
}
const memoAS = new Map();
let deadline = 0, timedOut = false;
function asWin(state, j, J) {
  const n = state.length;
  const masks = state.map(c => c >> 6), cnt = state.map(c => c & 63);
  if (j >= 4 && winningQuad(masks, cnt, n, j)) return true;
  if (j === J) return false;
  const key = J + '|' + j + ':' + state.join(',');
  const mm = memoAS.get(key);
  if (mm !== undefined) return mm;
  if (timedOut) return false;
  if (Date.now() > deadline) { timedOut = true; return false; }
  let total = 0; for (const c of cnt) total += c;
  const reqs = vectors(cnt, Math.min(T, total));
  const score = s => { let x = 0; for (let y = 0; y < n; y++) x += s[y] * popc(masks[y]); return -x; };
  reqs.sort((a, b) => score(a) - score(b));     // points of high degree first (keeps the replies triple-free)
  const b = 1 << j;
  let result = false;
  const a = new Array(n).fill(0), rest = new Array(n);
  for (const s of reqs) {
    for (let x = 0; x < n; x++) rest[x] = cnt[x] - s[x];
    let ok = true;
    const seen = new Set();
    const rec = (x, used) => {
      if (!ok) return;
      if (x === n) {
        const im = [], ic = [];
        for (let y = 0; y < n; y++) { if (a[y]) { im.push(masks[y] | b); ic.push(a[y]); } if (cnt[y] - a[y]) { im.push(masks[y]); ic.push(cnt[y] - a[y]); } }
        if (k - used) { im.push(b); ic.push(k - used); }
        const code = canon(im, ic, im.length, j + 1);
        const ck = code.join(',');
        if (seen.has(ck)) return;
        seen.add(ck);
        if (!asWin(code, j + 1, J)) ok = false;
        return;
      }
      for (let v = Math.min(rest[x], k - used); v >= 0 && ok; v--) { a[x] = v; rec(x + 1, used + v); }
      a[x] = 0;
    };
    rec(0, 0);
    if (timedOut) return false;
    if (ok) { result = true; break; }
  }
  memoAS.set(key, result);
  return result;
}
console.log(`C4  k=${k} T=${T} (T/k=${(T / k).toFixed(4)}): selection of four petals with a requester-winning configuration; ${FULL ? 'ANY four replies (exact four-petal value)' : 'triple-free quadruples only'}`);
for (let J = 4; J <= Jmax; J++) {
  const t0 = Date.now();
  deadline = t0 + limit * 1000; timedOut = false;
  const r = asWin([1 * 64 + k], 1, J);
  console.log(`  J=${J} replies (m = ${J + 3} requests): ${timedOut ? 'UNDECIDED (time limit)' : (r ? 'REQUESTER can always obtain four winning petals' : 'ADVERSARY can keep every four replies losing')}   states=${memoAS.size}, four-petal configurations evaluated ${quadCache.size} (R: ${[...quadCache.values()].filter(x => x).length}) [${((Date.now() - t0) / 1000).toFixed(1)}s]`);
  if (r && !timedOut) break;
}
'''
open('petal_select.js', 'w', encoding='utf-8').write(head + common + sel)
tables = r'''
// ---- C1, C2, C3 tables.   usage: node petal.js k T
const k = parseInt(process.argv[2]), T = parseInt(process.argv[3]);
const g = new Game(k, T);
const P = { 12: 3, 13: 5, 14: 9, 23: 6, 24: 10, 34: 12 };
console.log(`k=${k} T=${T} (T/k=${(T / k).toFixed(4)})`);
// C1(b): two pairs with cores a (petals 1,2) and b (petals 3,4); cross cells all 0 or all 1
for (const cross of [0, 1]) {
  const mism = [];
  let rows = 0, agree = 0;
  const grid = [];
  for (let a = 0; a + 2 * cross <= k; a++) {
    let line = '';
    for (let b = 0; b + 2 * cross <= k; b++) {
      const r = quadWin(g, [P[12], P[34], P[13], P[14], P[23], P[24]], [a, b, cross, cross, cross, cross]);
      const pred = Math.ceil(Lstar(a, b) - 1e-9) <= T;
      rows++; if (r === pred) agree++; else mism.push(`(a=${a},b=${b}: exact ${r ? 'R' : 'A'}, L*=${Lstar(a, b).toFixed(2)})`);
      line += r ? 'R' : 'A';
    }
    grid.push(`a=${String(a).padStart(2)}: ${line}`);
  }
  console.log(`C1(b) two pairs, cross cells = ${cross}: ${rows} configurations, prediction "R iff ceil(L*(a,b)) <= T" agrees on ${agree}`);
  console.log('   rows a = 0.., columns b = 0..   ' + grid.join(' | '));
  console.log('   disagreements: ' + (mism.join(' ') || 'none'));
}
// C1(c): triple-free configurations with pair cells from a grid of values
{
  const step = k <= 9 ? 1 : (k <= 12 ? 2 : 3);
  let n = 0, nR = 0, suffR = 0, suffTot = 0; const viol = []; const seen = new Set();
  const vals = []; for (let v = 0; v <= k; v += step) vals.push(v);
  for (const c12 of vals) for (const c34 of vals) for (const c13 of vals) for (const c24 of vals) for (const c14 of vals) for (const c23 of vals) {
    if (c12 + c13 + c14 > k || c12 + c23 + c24 > k || c13 + c23 + c34 > k || c14 + c24 + c34 > k) continue;
    const key = [[c12, c34].sort(), [c13, c24].sort(), [c14, c23].sort()].map(x => x.join('.')).sort().join('|');
    if (seen.has(key)) continue; seen.add(key);
    const r = quadWin(g, [P[12], P[34], P[13], P[24], P[14], P[23]], [c12, c34, c13, c24, c14, c23]);
    n++; if (r) nR++;
    const suff = (c12 + c34 <= T) && (c13 + c24 <= T) && (c14 + c23 <= T);
    if (suff) { suffTot++; if (r) suffR++; else viol.push(`(${c12},${c34};${c13},${c24};${c14},${c23})`); }
  }
  console.log(`C1(c) triple-free configurations on the grid step ${step}: ${n} configurations, requester wins ${nR}; of the ${suffTot} with all three loads c12+c34, c13+c24, c14+c23 <= T she wins ${suffR}` + (viol.length ? '; exceptions: ' + viol.slice(0, 12).join(' ') : ''));
}
// C2: one cluster: every point misses one petal (triple cells t) or two (pair cells p); symmetric family 3t + 3p = k
{
  const out = [];
  for (let t = 0; 3 * t <= k; t++) {
    const rem = k - 3 * t; if (rem % 3) continue; const p = rem / 3;
    const r = quadWin(g, [7, 11, 13, 14, 3, 5, 9, 6, 10, 12], [t, t, t, t, p, p, p, p, p, p]);
    out.push(`(triple cells ${t}, pair cells ${p}; pairwise overlap ${2 * t + p}): ${r ? 'R' : 'A'}`);
  }
  for (let t = 1; 3 * t <= k; t++) {
    const r = quadWin(g, [7, 11, 13, 14], [t, t, t, t]);
    out.push(`(triple cells ${t} only, rest singles; pairwise overlap ${2 * t}): ${r ? 'R' : 'A'}`);
  }
  console.log('C2 one-cluster configurations: ' + out.join('  '));
}
// C3: three cluster petals 1,2,3 with common core c3 and pair-only cells q each, outside petal 4 with one point in each
{
  const rowsR = [];
  for (let c3 = 0; c3 <= k; c3++) {
    let line = '';
    for (let q = 0; c3 + 2 * q + 1 <= k; q++) {
      const r = quadWin(g, [7, 3, 5, 6, 9, 10, 12, 8], [c3, q, q, q, 1, 1, 1, k - 3]);
      line += r ? 'R' : 'A';
    }
    if (line) rowsR.push(`c3=${c3}: ${line}`);
  }
  console.log(`C3 three cluster petals (core c3; columns pair-only cells q = 0,1,2,..) + outside petal: ` + rowsR.join(' | ') + `   [necessary bound from TWIN 15.5: c3 <= T - k/3 = ${(T - k / 3).toFixed(2)}]`);
}
console.log(`  (four-petal configurations evaluated: ${quadCache.size}, engine time ${(quadTime / 1000).toFixed(0)}s)`);
'''
open('petal.js', 'w', encoding='utf-8').write(head + common + tables)
print("written")
