// differential test: fast engine vs original exact7d.js Game on random states at levels 3,4,5
'use strict';
const fs = require('fs'), vm = require('vm');
let src = fs.readFileSync(__dirname + '/../fresh_c/exact7d.js', 'utf8');
src = src.slice(0, src.indexOf('const k = parseInt(process.argv[2]);'));
const ctx = {}; vm.createContext(ctx);
vm.runInContext(src + '\nthis.Game=Game; this.canon=canon;', ctx);
const { Engine } = require('./engine.js');
let seed = +process.argv[2] || 1; const rnd = () => { seed = (Math.imul(seed, 1103515245) + 12345) & 0x7fffffff; return seed / 0x7fffffff; };
const trials = +process.argv[3] || 300;
let bad = 0, cnt = 0, wins = 0;
for (let t = 0; t < trials; t++) {
  const i = 3 + Math.floor(rnd() * 3);                 // 3,4,5 edges
  const k = 4 + Math.floor(rnd() * 5);                 // 4..8
  const T = Math.max(2, k - 1 - Math.floor(rnd() * 3));
  const ntypes = 3 + Math.floor(rnd() * 7);
  const used = new Set(), masks = [], counts = [];
  for (let x = 0; x < ntypes; x++) {
    const m = 1 + Math.floor(rnd() * ((1 << i) - 1));
    if (used.has(m)) continue; used.add(m); masks.push(m); counts.push(1 + Math.floor(rnd() * 3));
  }
  // relevance filter at i edges
  const full = (1 << i) - 1, rm = [], rc = [];
  for (let x = 0; x < masks.length; x++) { const need = full & ~masks[x]; if (masks.some((m2, y) => (m2 & need) === need)) { rm.push(masks[x]); rc.push(counts[x]); } }
  if (!rm.length) continue;
  const tot = rc.reduce((a, b) => a + b, 0);
  if (tot <= T || tot > 3 * k) continue;
  for (const pb of [true, false]) {
    const og = new ctx.Game(k, T); og.usePairBound = pb;
    const code = ctx.canon(rm, rc, rm.length, i);
    const r0 = og.win(code, i);
    const ng = new Engine(k, T, { pairBound: pb });
    const c2 = ng.canonArr(rm, rc, i);
    const r1 = ng.win(Int32Array.from(c2), c2.length, i);
    const ng2 = new Engine(k, T, { pairBound: pb, fastLast: false });
    const r2 = ng2.win(Int32Array.from(c2), c2.length, i);
    cnt++; if (r0) wins++;
    if (r0 !== r1 || r0 !== r2) { bad++; console.log('MISMATCH', { i, k, T, rm, rc, pb, old: r0, fast: r1, nofast: r2 }); }
  }
}
console.log(`tests ${cnt}, requester wins ${wins}, mismatches ${bad}`);
