// CORE 113: local search for a good seven (seven members covering all pairs of V) in an explicit co-edge family.
// [heuristic: "not found" is NOT a proof]. A found seven is re-checked pair by pair before printing.
// Usage: node gs_search.js famfile n restarts steps seed   -> "G m1 ... m7" or "NONE"
const fs = require('fs');
const [file, nS, rS, sS, seedS] = process.argv.slice(2); const n = +nS, restarts = +rS, steps = +sS; let seed = +seedS || 1;
const rnd = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x80000000; };
const fam = fs.readFileSync(file, 'utf8').trim().split(/\s+/).map(Number);
const pairs = []; for (let x = 0; x < n; x++) for (let y = x + 1; y < n; y++) pairs.push([x, y]);
const W = Math.ceil(pairs.length / 32);
const cov = fam.map(K => { const v = new Uint32Array(W); pairs.forEach(([x, y], i) => { if ((K >> x & 1) && (K >> y & 1)) v[i >> 5] |= 1 << (i & 31); }); return v; });
const pc32 = v => { v = v - ((v >>> 1) & 0x55555555); v = (v & 0x33333333) + ((v >>> 2) & 0x33333333); return (((v + (v >>> 4)) & 0x0F0F0F0F) * 0x01010101) >>> 24; };
const total = pairs.length; const base = new Uint32Array(W);
function score(base, v) { let s = 0; for (let w = 0; w < W; w++) s += pc32(base[w] | v[w]); return s; }
let best = null;
for (let r = 0; r < restarts && !best; r++) {
  const cur = Array.from({ length: 7 }, () => Math.floor(rnd() * fam.length));
  for (let st = 0; st < steps; st++) {
    const i = Math.floor(rnd() * 7); base.fill(0);
    for (let j = 0; j < 7; j++) if (j !== i) for (let w = 0; w < W; w++) base[w] |= cov[cur[j]][w];
    if (rnd() < 0.15) cur[i] = Math.floor(rnd() * fam.length);
    else { let bv = -1, bi = [];
      for (let a = 0; a < fam.length; a++) { const v = score(base, cov[a]); if (v > bv) { bv = v; bi = [a]; } else if (v === bv && bi.length < 50) bi.push(a); }
      cur[i] = bi[Math.floor(rnd() * bi.length)]; }
    base.fill(0); for (let j = 0; j < 7; j++) for (let w = 0; w < W; w++) base[w] |= cov[cur[j]][w];
    if (score(base, new Uint32Array(W)) === total) { best = cur.map(j => fam[j]); break; }
  }
}
if (best) { const ok = pairs.every(([x, y]) => best.some(K => (K >> x & 1) && (K >> y & 1))); if (!ok) throw new Error('bad seven'); console.log('G ' + best.join(' ')); }
else console.log('NONE');
