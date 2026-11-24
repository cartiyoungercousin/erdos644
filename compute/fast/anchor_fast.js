// Fast anchor-selection solver (port of compute/fresh_c/anchor_select.js onto engine.js), same certificate format.
// usage: node anchor_fast.js k T Jmax [timeLimitSeconds] [certDir]
'use strict';
const fs = require('fs'), path = require('path');
const { Engine, permutations } = require('./engine.js');
const k = parseInt(process.argv[2]);
const T = parseInt(process.argv[3]);
const Jmax = parseInt(process.argv[4]);
const limit = process.argv[5] ? parseFloat(process.argv[5]) : 1e9;
const certDir = process.argv[6] || __dirname;
const g = new Engine(k, T, { maxEntries: +process.env.MAXE || 20e6, maxEntries5: +process.env.MAXE5 || 20e6 });
const W = new Map();
let wTime = 0;
let timedOut = false;
const canonA = (im, ic, ie) => g.canonArr(im, ic, ie);
function vectors(caps, total) {
  const n = caps.length, suffix = new Array(n + 1).fill(0);
  for (let j = n - 1; j >= 0; j--) suffix[j] = suffix[j + 1] + caps[j];
  const out = [], cur = new Array(n).fill(0);
  (function rec(j, rem) {
    if (j === n) { if (rem === 0) out.push(cur.slice()); return; }
    const lo = Math.max(0, rem - suffix[j + 1]), hi = Math.min(caps[j], rem);
    for (let v = hi; v >= lo; v--) { cur[j] = v; rec(j + 1, rem - v); }
    cur[j] = 0;
  })(0, total);
  return out;
}
function anchoredState(p12, p13, p23) {
  const c = [k - p12 - p13, k - p12 - p23, k - p13 - p23];
  if (c[0] < 0 || c[1] < 0 || c[2] < 0) return null;
  const masks = [3, 5, 6, 1, 2, 4], counts = [p12, p13, p23, c[0], c[1], c[2]];
  const rm = [], rc = [];
  for (let x = 0; x < 6; x++) {
    if (!counts[x]) continue;
    const need = 7 & ~masks[x];
    let ok = false;
    for (let y = 0; y < 6; y++) if (counts[y] && (masks[y] & need) === need) { ok = true; break; }
    if (ok) { rm.push(masks[x]); rc.push(counts[x]); }
  }
  return canonA(rm, rc, 3);
}
const deadlineAll = Date.now() + limit * 1000;
function shapeWin(p12, p13, p23) {
  const key = p12 + ',' + p13 + ',' + p23;
  let r = W.get(key);
  if (r !== undefined) return r;
  const st = anchoredState(p12, p13, p23);
  if (!st) { W.set(key, false); return false; }
  const t0 = Date.now();
  g.deadline = deadlineAll; g.timedOut = false;
  r = g.win(Int32Array.from(st), st.length, 3);
  if (g.timedOut) { timedOut = true; return false; }
  wTime += Date.now() - t0;
  W.set(key, r);
  if (process.env.AS_VERBOSE) console.log(`    shape (${key}) |V|=${3 * k - p12 - p13 - p23}: ${r ? 'R' : 'A'}  [${((Date.now() - t0) / 1000).toFixed(1)}s] nodes=${g.nodes}`);
  return r;
}
function winningTriple(masks, cnt, n, j) {
  for (let a = 0; a < j; a++) for (let b = a + 1; b < j; b++) for (let c = b + 1; c < j; c++) {
    let pab = 0, pac = 0, pbc = 0, tri = 0;
    for (let x = 0; x < n; x++) {
      const m = masks[x];
      const ia = (m >> a) & 1, ib = (m >> b) & 1, ic = (m >> c) & 1;
      if (ia && ib && ic) { tri += cnt[x]; break; }
      if (ia && ib) pab += cnt[x]; else if (ia && ic) pac += cnt[x]; else if (ib && ic) pbc += cnt[x];
    }
    if (tri) continue;
    const v = [pab, pac, pbc].sort((x, y) => y - x);
    if (shapeWin(v[0], v[1], v[2])) return [a + 1, b + 1, c + 1, v];
    if (timedOut) return null;
  }
  return null;
}
const memoAS = new Map(), bestAS = new Map();
function asWin(state, j, J) {
  const n = state.length;
  const masks = state.map(c => c >> 6), cnt = state.map(c => c & 63);
  if (j >= 3 && winningTriple(masks, cnt, n, j)) return true;
  if (timedOut) return false;
  if (j === J) return false;
  const key = J + '|' + j + ':' + state.join(',');
  const mm = memoAS.get(key);
  if (mm !== undefined) return mm;
  let total = 0; for (const c of cnt) total += c;
  const reqs = vectors(cnt, Math.min(T, total));
  const score = s => {
    let worst = 0;
    for (let e = 0; e < j; e++) { let left = 0; for (let x = 0; x < n; x++) if ((masks[x] >> e) & 1) left += cnt[x] - s[x]; if (left > worst) worst = left; }
    return worst;
  };
  reqs.sort((a, b) => score(a) - score(b));
  const b = 1 << j;
  let result = false;
  const a = new Array(n).fill(0), rest = new Array(n);
  for (const s of reqs) {
    for (let x = 0; x < n; x++) rest[x] = cnt[x] - s[x];
    let ok = true;
    const seen = new Set();
    const test = (used) => {
      const im = [], ic = [];
      for (let x = 0; x < n; x++) {
        if (a[x]) { im.push(masks[x] | b); ic.push(a[x]); }
        if (cnt[x] - a[x]) { im.push(masks[x]); ic.push(cnt[x] - a[x]); }
      }
      if (k - used) { im.push(b); ic.push(k - used); }
      const code = canonA(im, ic, j + 1);
      const ck = code.join(',');
      if (seen.has(ck)) return true;
      seen.add(ck);
      return asWin(code, j + 1, J);
    };
    const rec = (x, used) => {
      if (!ok) return;
      if (x === n) { if (!test(used)) ok = false; return; }
      const hi = Math.min(rest[x], k - used);
      for (let v = hi; v >= 0 && ok; v--) { a[x] = v; rec(x + 1, used + v); }
      a[x] = 0;
    };
    rec(0, 0);
    if (timedOut) return false;
    if (ok) { result = true; bestAS.set(key, s.slice()); break; }
  }
  memoAS.set(key, result);
  return result;
}

// ------------------------------------------------------------------ certificate of a requester win (format of anchor_select.js)
const GP = {};
function globalCanon(masks, counts, i) {
  if (!GP[i]) GP[i] = permutations([...Array(i).keys()]);
  let best = null;
  const n = masks.length;
  for (const p of GP[i]) {
    const tmp = new Array(n);
    for (let x = 0; x < n; x++) { let v = 0; for (let b = 0; b < i; b++) if ((masks[x] >> b) & 1) v |= 1 << p[b]; tmp[x] = [v * 64 + counts[x], x]; }
    tmp.sort((a, b) => a[0] - b[0]);
    let less = best === null;
    if (!less) for (let x = 0; x < n; x++) { if (tmp[x][0] < best[x][0]) { less = true; break; } if (tmp[x][0] > best[x][0]) break; }
    if (less) best = tmp;
  }
  return best;
}
function writeCertificate(J) {
  const cert = { k, T, J, as: {}, shapes: {} };
  const shapesUsed = new Set(), seenAS = new Set();
  (function dfs(state, j) {
    const n = state.length;
    const masks = state.map(c => c >> 6), cnt = state.map(c => c & 63);
    if (j >= 3) { const w = winningTriple(masks, cnt, n, j); if (w) { shapesUsed.add(w[3].join(',')); return; } }
    const key = J + '|' + j + ':' + state.join(',');
    if (seenAS.has(key)) return;
    seenAS.add(key);
    const s = bestAS.get(key);
    if (!s) throw new Error('missing AS move at ' + key);
    const gc = globalCanon(masks, cnt, j);
    cert.as[j + ':' + gc.map(x => x[0]).join(',')] = gc.map(x => s[x[1]]);
    const b = 1 << j, a = new Array(n).fill(0), rest = cnt.map((c, x) => c - s[x]);
    const seen = new Set();
    (function rec(x, used) {
      if (x === n) {
        const im = [], ic = [];
        for (let y = 0; y < n; y++) { if (a[y]) { im.push(masks[y] | b); ic.push(a[y]); } if (cnt[y] - a[y]) { im.push(masks[y]); ic.push(cnt[y] - a[y]); } }
        if (k - used) { im.push(b); ic.push(k - used); }
        const code = canonA(im, ic, j + 1);
        const ck = code.join(',');
        if (!seen.has(ck)) { seen.add(ck); dfs(code, j + 1); }
        return;
      }
      for (let v = Math.min(rest[x], k - used); v >= 0; v--) { a[x] = v; rec(x + 1, used + v); }
      a[x] = 0;
    })(0, 0);
  })([1 * 64 + k], 1);
  for (const sh of shapesUsed) {
    const [p12, p13, p23] = sh.split(',').map(Number);
    const nodes = {}, seenA = new Set();
    (function dfsA(state, i) {
      let tot = 0; for (const cc of state) tot += cc & 63;
      if (tot <= T) return;
      const key = i + ':' + state.join(',');
      if (seenA.has(key)) return;
      seenA.add(key);
      const n = state.length, masks = state.map(cc => cc >> 6), cnt = state.map(cc => cc & 63);
      const mv = g.moveFor(Int32Array.from(state), n, i);
      if (!mv) throw new Error('missing anchored move at ' + key + ' shape ' + sh);
      let s;
      if (mv.req) s = mv.req;
      else {
        s = new Array(n).fill(0);
        let spare = T;
        for (let x = 0; x < n; x++) if (mv.block.includes(masks[x])) { s[x] = cnt[x]; spare -= cnt[x]; }
        let nb = 0;
        for (let x = 0; x < n; x++) if (!s[x]) { const need = 31 & ~masks[x]; for (let y = 0; y < n; y++) if ((masks[y] & need) === need) nb |= 1 << y; }
        for (let x = 0; x < n && spare > 0; x++) if (!s[x] && !((nb >> x) & 1)) { const t = Math.min(spare, cnt[x]); s[x] = t; spare -= t; }
        for (let x = 0; x < n && spare > 0; x++) if (s[x] < cnt[x]) { const t = Math.min(spare, cnt[x] - s[x]); s[x] += t; spare -= t; }
      }
      const gc = globalCanon(masks, cnt, i);
      nodes[i + ':' + gc.map(x => x[0]).join(',')] = gc.map(x => s[x[1]]);
      if (i === 5) return;
      for (const ch of g.children(Int32Array.from(state), n, i, s)) dfsA(ch, i + 1);
    })(anchoredState(p12, p13, p23), 3);
    cert.shapes[sh] = nodes;
  }
  const fn = path.join(certDir, `cert_k${k}_T${T}_J${J}.json`);
  fs.writeFileSync(fn, JSON.stringify(cert));
  let nA = 0; for (const sh in cert.shapes) nA += Object.keys(cert.shapes[sh]).length;
  console.log(`    certificate written: ${fn}  (anchor-selection nodes ${Object.keys(cert.as).length}, winning shapes used ${Object.keys(cert.shapes).length}, anchored-game nodes ${nA})`);
  return fn;
}
console.log(`k=${k} T=${T} (T/k=${(T / k).toFixed(4)}): anchored shapes evaluated on demand (fast engine)`);
const T00 = Date.now();
for (let J = 3; J <= Jmax; J++) {
  const t0 = Date.now();
  timedOut = false;
  const r = asWin([1 * 64 + k], 1, J);
  const secs = ((Date.now() - t0) / 1000).toFixed(1);
  console.log(`  anchor selection among J=${J} replies (m = ${J + 4} requests): ${timedOut ? 'UNDECIDED (time limit)' : (r ? 'REQUESTER can always obtain a winning anchor triple' : 'ADVERSARY can keep every triple of replies losing')}   states=${memoAS.size} [${secs}s]`);
  console.log(`    shapes evaluated so far: ${W.size} (R: ${[...W.values()].filter(x => x).length}); anchored-game time ${(wTime / 1000).toFixed(0)}s; engine nodes ${g.nodes}, table ${g.t34.count}+${g.t5.count}, resets ${g.t34.resets - 1}/${g.t5.resets - 1}`);
  if (timedOut) break;
  if (r) { writeCertificate(J); break; }
}
const lose = [...W.entries()].filter(e => !e[1]).map(e => '(' + e[0] + ')'), winS = [...W.entries()].filter(e => e[1]).map(e => '(' + e[0] + ')');
console.log('  shapes found losing for her: ' + lose.join(' '));
console.log('  shapes found winning for her: ' + winS.join(' '));
console.log(`  total ${((Date.now() - T00) / 1000).toFixed(1)}s`);
