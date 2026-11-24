// usage: node anchor_table_fast.js k T [timeLimitSecondsPerShape]  -- table of the anchored game over all shapes (as anchor.js)
'use strict';
const { Engine } = require('./engine.js');
const k = +process.argv[2], T = +process.argv[3], limit = process.argv[4] ? +process.argv[4] : 1e9;
const g = new Engine(k, T);
const t00 = Date.now(); const losing = []; let nR = 0, nA = 0, nQ = 0, n = 0;
for (let p12 = 0; p12 <= k; p12++) for (let p13 = 0; p13 <= p12; p13++) for (let p23 = 0; p23 <= p13; p23++) {
  if (p12 + p13 > k) continue;
  const c = [k - p12 - p13, k - p12 - p23, k - p13 - p23];
  if (c[0] < 0 || c[1] < 0 || c[2] < 0) continue;
  const masks = [3, 5, 6, 1, 2, 4], counts = [p12, p13, p23, c[0], c[1], c[2]], rm = [], rc = [];
  for (let x = 0; x < 6; x++) { if (!counts[x]) continue; const need = 7 & ~masks[x]; let ok = false; for (let y = 0; y < 6; y++) if (counts[y] && (masks[y] & need) === need) { ok = true; break; } if (ok) { rm.push(masks[x]); rc.push(counts[x]); } }
  const st = g.canonArr(rm, rc, 3);
  g.deadline = Date.now() + limit * 1000; g.timedOut = false;
  const r = g.win(Int32Array.from(st), st.length, 3);
  n++;
  const V = 3 * k - p12 - p13 - p23;
  if (g.timedOut) { nQ++; losing.push(`(${p12},${p13},${p23};${V}?)`); } else if (r) nR++; else { nA++; losing.push(`(${p12},${p13},${p23};${V})`); }
}
console.log(`k=${k} T=${T}: shapes=${n}, requester wins ${nR}, adversary wins ${nA}, undecided ${nQ} [${((Date.now() - t00) / 1000).toFixed(0)}s]`);
console.log('  adversary-winning shapes (p12,p13,p23;|V|): ' + (losing.length ? losing.join(' ') : 'none'));
