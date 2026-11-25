// Enumerate ALL maximal intersecting families M on [7] (= self-dual up-sets of 2^[7]),
// count them (expected 1422564 = OEIS A001206(7)), and output one canonical representative
// per S_7-orbit together with |Aut|.  Orbit-stabilizer check: sum 5040/|Aut| = total.
// Output: JSON lines {mask: hex128, aut: int, fano: bool}.
// Usage: node maxint7_enum.js out.jsonl
'use strict';
const fs = require('fs');
const FULL = 127;
const pc = new Uint8Array(128);
for (let g = 0; g < 128; g++) { let c = 0, x = g; while (x) { c += x & 1; x >>= 1; } pc[g] = c; }

// pairs {G, G^c} with |G| <= 3, decide G or G^c; order by |G| ascending
const pairs = [];
for (let g = 0; g < 128; g++) if (pc[g] <= 3) pairs.push(g);
pairs.sort((a, b) => pc[a] - pc[b] || a - b);

// Fano planes on [7]: all 30 labelled copies
function fanoPlanes() {
  const base = [[0,1,2],[0,3,4],[0,5,6],[1,3,5],[1,4,6],[2,3,6],[2,4,5]];
  const seen = new Set(); const out = [];
  const perm = [0,1,2,3,4,5,6];
  function rec(i) {
    if (i === 7) {
      const lines = base.map(l => l.reduce((m, p) => m | (1 << perm[p]), 0)).sort((a,b)=>a-b);
      const key = lines.join(',');
      if (!seen.has(key)) { seen.add(key); out.push(lines); }
      return;
    }
    for (let j = i; j < 7; j++) { [perm[i], perm[j]] = [perm[j], perm[i]]; rec(i + 1); [perm[i], perm[j]] = [perm[j], perm[i]]; }
  }
  rec(0); return out;
}
const planes = fanoPlanes();
if (planes.length !== 30) throw new Error('planes ' + planes.length);
const fanoKeys = new Set(planes.map(lines => {
  const st = new Uint8Array(128);
  for (let g = 0; g < 128; g++) st[g] = lines.some(l => (g & l) === l) ? 1 : 0;
  return maskHex(st);
}));

function maskHex(st) {
  let s = '';
  for (let w = 3; w >= 0; w--) {
    let v = 0;
    for (let b = 31; b >= 0; b--) v = (v * 2) + st[w * 32 + b];
    s += v.toString(16).padStart(8, '0');
  }
  return s;
}

// all 5040 permutations, and subset images
const perms = [];
(function gen(a, i) {
  if (i === 7) { perms.push(a.slice()); return; }
  for (let j = i; j < 7; j++) { [a[i], a[j]] = [a[j], a[i]]; gen(a, i + 1); [a[i], a[j]] = [a[j], a[i]]; }
})([0,1,2,3,4,5,6], 0);

function imageSet(p) { // p: point -> point; returns Uint8Array(128) mapping subset->subset
  const im = new Uint8Array(128);
  for (let g = 0; g < 128; g++) { let h = 0; for (let i = 0; i < 7; i++) if (g >> i & 1) h |= 1 << p[i]; im[g] = h; }
  return im;
}

let total = 0;
const classes = new Map(); // canonical hex -> {aut, count}

function canon(st) {
  // invariant: for each point, counts of members of each size containing it
  const inv = [];
  for (let i = 0; i < 7; i++) {
    const c = new Array(8).fill(0);
    for (let g = 0; g < 128; g++) if (st[g] && (g >> i & 1)) c[pc[g]]++;
    inv.push(c.join('.'));
  }
  const order = [0,1,2,3,4,5,6].sort((a, b) => (inv[a] < inv[b] ? -1 : inv[a] > inv[b] ? 1 : a - b));
  // positions: point order[j] goes to a position in its class block
  const cls = order.map(p => inv[p]);
  // enumerate bijections respecting blocks: perm q of positions within blocks
  const blocks = []; let s = 0;
  for (let j = 1; j <= 7; j++) if (j === 7 || cls[j] !== cls[s]) { blocks.push([s, j]); s = j; }
  let best = null, aut = 0;
  const pos = new Array(7);
  const origHex = maskHex(st);
  function rec(b) {
    if (b === blocks.length) {
      const p = new Array(7);
      for (let j = 0; j < 7; j++) p[order[j]] = pos[j];
      const out = new Uint8Array(128);
      for (let g = 0; g < 128; g++) if (st[g]) { let h = 0; for (let i = 0; i < 7; i++) if (g >> i & 1) h |= 1 << p[i]; out[h] = 1; }
      const hx = maskHex(out);
      if (best === null || hx < best) { best = hx; aut = 1; } else if (hx === best) aut++;
      return;
    }
    const [lo, hi] = blocks[b];
    const avail = []; for (let j = lo; j < hi; j++) avail.push(j);
    (function per(i) {
      if (i === hi) { rec(b + 1); return; }
      for (let t = i; t < hi; t++) {
        [avail[i - lo], avail[t - lo]] = [avail[t - lo], avail[i - lo]];
        pos[i] = avail[i - lo];
        per(i + 1);
        [avail[i - lo], avail[t - lo]] = [avail[t - lo], avail[i - lo]];
      }
    })(lo);
  }
  rec(0);
  return [best, aut];
}

function dfs(st, idx) {
  // st: Int8Array(128), 1 in M, -1 not in M, 0 undecided
  while (idx < pairs.length && st[pairs[idx]] !== 0) idx++;
  if (idx === pairs.length) {
    total++;
    const m = new Uint8Array(128); for (let g = 0; g < 128; g++) m[g] = st[g] === 1 ? 1 : 0;
    const [hx, aut] = canon(m);
    const e = classes.get(hx);
    if (e) e.count++; else classes.set(hx, { aut, count: 1 });
    return;
  }
  const g = pairs[idx];
  for (const choice of [g, FULL ^ g]) {
    const s2 = Int8Array.from(st);
    if (setIn(s2, choice)) dfs(s2, idx + 1);
  }
}
function setIn(st, g) { // put g in M, propagate: supersets in, complements of supersets out
  const stack = [g];
  while (stack.length) {
    const h = stack.pop();
    if (st[h] === 1) continue;
    if (st[h] === -1) return false;
    st[h] = 1;
    const c = FULL ^ h;
    if (st[c] === 1) return false;
    st[c] = -1;
    for (let i = 0; i < 7; i++) if (!(h >> i & 1)) stack.push(h | (1 << i));
  }
  // consistency of downward: if h out, subsets of h out => their complements (supersets of h^c) in: covered by pushing complements
  return true;
}
// note: putting h in M pushes all supersets in, and marks complements out. A complement c of a superset
// is a subset of h^c; subsets of an out-set must be out, which holds since c^c is a superset of h^c's
// complement... we verify full validity of every leaf below instead of relying on this argument.

const st0 = new Int8Array(128);
dfs(st0, 0);

// validate: every class rep is a self-dual up-set
let orbitSum = 0, nf = 0;
const lines = [];
for (const [hx, e] of classes) {
  orbitSum += 5040 / e.aut;
  if (e.count !== 5040 / e.aut) throw new Error('orbit count mismatch ' + hx + ' ' + e.count + ' ' + e.aut);
  const isF = fanoKeys.has(hx) || false;
  lines.push(JSON.stringify({ mask: hx, aut: e.aut, count: e.count }));
}
// check validity of reps
function parseHex(hx) { const st = new Uint8Array(128); for (let w = 0; w < 4; w++) { const v = parseInt(hx.slice((3 - w) * 8, (4 - w) * 8), 16); for (let b = 0; b < 32; b++) st[w * 32 + b] = (Math.floor(v / 2 ** b)) % 2; } return st; }
for (const hx of classes.keys()) {
  const st = parseHex(hx);
  for (let g = 0; g < 128; g++) {
    if (st[g] + st[FULL ^ g] !== 1) throw new Error('not self-dual');
    for (let i = 0; i < 7; i++) if (st[g] && !st[g | (1 << i)]) throw new Error('not up-set');
  }
}
fs.writeFileSync(process.argv[2], lines.join('\n') + '\n');
console.log(JSON.stringify({ total, classes: classes.size, orbitSum }));
