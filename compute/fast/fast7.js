// usage: node fast7.js k T[,T2..] [N] [seconds]   -- 7-request game, one fixed edge, ground set of N points (default 2k)
'use strict';
const { Engine } = require('./engine.js');
const k = parseInt(process.argv[2]);
const Ts = process.argv[3].split(',').map(Number);
const N = process.argv[4] ? parseInt(process.argv[4]) : 2 * k;
const limit = process.argv[5] ? parseFloat(process.argv[5]) : 1e9;
function fmtMask(m) { let s = ''; for (let b = 0; b < 6; b++) if ((m >> b) & 1) s += (b + 1); return s || '-'; }
function fmtState(st) { return '{' + st.map(c => fmtMask(c >> 6) + ':' + (c & 63)).join(', ') + '}'; }
function mainLine(g, root) {
  const lines = []; let st = root, i = 1;
  for (;;) {
    let tot = 0; for (const c of st) tot += c & 63;
    if (tot <= g.T) { lines.push(`  after ${i} edges: |D| = ${tot} <= T, types ${fmtState(st)} -> request D, win`); break; }
    const mv = g.moveFor(Int32Array.from(st), st.length, i);
    if (!mv) { lines.push(`  after ${i} edges: |D| = ${tot} types ${fmtState(st)} (no move)`); break; }
    if (mv.block) { lines.push(`  after ${i} edges: |D| = ${tot} types ${fmtState(st)}  FINAL request: all of types [${mv.block.map(fmtMask).join(', ')}] + spare`); break; }
    const reqStr = st.map((c, j) => mv.req[j] ? fmtMask(c >> 6) + ':' + mv.req[j] : null).filter(x => x).join(', ');
    lines.push(`  after ${i} edges: |D| = ${tot} types ${fmtState(st)}  request {${reqStr}}`);
    const ch = g.children(Int32Array.from(st), st.length, i, mv.req);
    if (!ch.length) { lines.push('  every reply leaves |D| <= T'); break; }
    // heaviest child first, as in the originals
    ch.sort((x, y) => y.reduce((s, c) => s + (c & 63), 0) - x.reduce((s, c) => s + (c & 63), 0));
    st = ch[0]; i++;
  }
  return lines;
}
for (const T of Ts) {
  const t0 = Date.now();
  const g = new Engine(k, T);
  g.deadline = t0 + limit * 1000;
  const pool = N - k;
  const root = pool > 0 ? g.canonArr([1, 0], [k, pool], 1) : g.canonArr([1], [k], 1);
  const r = g.win(Int32Array.from(root), root.length, 1);
  const secs = ((Date.now() - t0) / 1000).toFixed(1);
  if (g.timedOut) { console.log(`k=${k} T=${T} N=${N}: UNDECIDED (limit ${limit}s) nodes=${g.nodes}`); continue; }
  console.log(`k=${k} T=${T} N=${N}: ${r ? 'REQUESTER wins' : 'ADVERSARY wins'}   states=${g.states()} nodes=${g.nodes} pruned=${g.pruned} resets=${g.t34.resets - 1}/${g.t5.resets - 1} [${secs}s]`);
  if (r && process.env.LINE) for (const ln of mainLine(g, root)) console.log(ln);
}
