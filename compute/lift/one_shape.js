// usage: node one_shape.js k T p12 p13 p23 limit
const { Engine } = require(__dirname + '/../fast/engine.js');
const [k, T, p12, p13, p23, limit] = process.argv.slice(2).map(Number);
const g = new Engine(k, T);
const c = [k - p12 - p13, k - p12 - p23, k - p13 - p23];
const masks = [3, 5, 6, 1, 2, 4], counts = [p12, p13, p23, c[0], c[1], c[2]], rm = [], rc = [];
for (let x = 0; x < 6; x++) { if (!counts[x]) continue; const need = 7 & ~masks[x]; let ok = false; for (let y = 0; y < 6; y++) if (counts[y] && (masks[y] & need) === need) { ok = true; break; } if (ok) { rm.push(masks[x]); rc.push(counts[x]); } }
const st = g.canonArr(rm, rc, 3);
g.deadline = Date.now() + limit * 1000; g.timedOut = false;
const t0 = Date.now();
const r = g.win(Int32Array.from(st), st.length, 3);
console.log(`(${k},${T}) shape (${p12},${p13},${p23}) |V|=${3*k-p12-p13-p23}: ${g.timedOut ? 'TIMEOUT' : (r ? 'REQUESTER' : 'ADVERSARY')} ${(Date.now()-t0)/1000}s`);
