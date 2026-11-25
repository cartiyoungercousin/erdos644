// SATURATION Task 1(a): exact co-type (spectrum) enumeration of "good sevens" with NON-uniform member sizes and
// per-member constraints on |K_i ∩ X|. [computed exact, exhaustive]
// A good seven = 7 sets K_0..K_6 ⊆ V (repetition allowed) covering every pair {u,v} of V (u = v allowed), i.e. the
// co-types I_v = {i : v ∈ K_i} are pairwise intersecting (and nonempty). Up to relabelling points, this is the same as
// nonnegative counts x_I (points of X with co-type I), y_I (points of Y) with intersecting support, Σx = |X|, Σy = |Y|,
// deg_i(x + y) = s_i, and deg_i(x) satisfying cons_i ('odd' | 'even' | 'any' | an integer).
// Hand facts: |I| = 1 impossible if s_i < n; I = {i,j} impossible if s_i + s_j < n (checked below, else abort).
// Hence Σ_v (|I_v| - 3) = Σ s_i - 3n =: E, carried by the heavy co-types (|I| >= 4).
// Usage: node spectrum_gen.js '<json>'  with json {n, xs, sizes:[7], cons:[7], maxWit}
const P = JSON.parse(process.argv[2]);
const { n, xs } = P, s = P.sizes, cons = P.cons, maxWit = P.maxWit ?? 3;
const pc = m => { let r = 0; while (m) { m &= m - 1; r++; } return r; };
for (let i = 0; i < 7; i++) { if (s[i] >= n) throw new Error('size >= n'); for (let j = i + 1; j < 7; j++) if (s[i] + s[j] >= n) throw new Error('pair types possible; model not valid'); }
const E = s.reduce((a, b) => a + b, 0) - 3 * n;
console.log(`n=${n} |X|=${xs} sizes=${s} cons=${JSON.stringify(cons)} excess E=${E}`);
if (E < 0) { console.log('RESULT: E < 0, NO good seven [exact]'); process.exit(0); }
// symmetry group: permutations of [7] preserving (s_i, cons_i)
const perms = []; (function gen(a, used) { if (a.length === 7) { if (a.every((p, i) => s[p] === s[i] && String(cons[p]) === String(cons[i]))) perms.push(a.slice()); return; }
  for (let i = 0; i < 7; i++) if (!used[i]) { used[i] = 1; a.push(i); gen(a, used); a.pop(); used[i] = 0; } })([], []);
const ptab = perms.map(p => { const t = new Uint8Array(128); for (let m = 0; m < 128; m++) { let r = 0; for (let i = 0; i < 7; i++) if (m >> i & 1) r |= 1 << p[i]; t[m] = r; } return t; });
console.log(`symmetry group order ${perms.length}`);
const heavyMasks = []; for (let m = 0; m < 128; m++) if (pc(m) >= 4) heavyMasks.push(m);
const heavies = new Map();
(function gen(start, ex, cur) {
  if (ex === E) { let best = null;
    for (const t of ptab) { const q = cur.map(m => t[m]).sort((a, b) => a - b).join(','); if (best === null || q < best) best = q; }
    if (!heavies.has(best)) heavies.set(best, best === '' ? [] : best.split(',').map(Number)); return; }
  for (let j = start; j < heavyMasks.length; j++) { const m = heavyMasks[j], e = pc(m) - 3; if (ex + e > E) continue;
    if (cur.some(q => (q & m) === 0)) continue; cur.push(m); gen(j, ex + e, cur); cur.pop(); }
})(0, 0, []);
console.log(`heavy multisets up to symmetry: ${heavies.size}`);
const triples = []; for (let m = 0; m < 128; m++) if (pc(m) === 3) triples.push(m);
// X-split DP: state = (parity mask over parity-constrained members, exact degrees of integer-constrained members, Σx)
const intIdx = [], parIdx = []; for (let i = 0; i < 7; i++) { if (typeof cons[i] === 'number') intIdx.push(i); else if (cons[i] !== 'any') parIdx.push(i); }
function splitSolve(types) { // returns x-assignment array or null
  let layer = new Map(); layer.set(JSON.stringify([0, intIdx.map(() => 0), 0]), null); const layers = [layer];
  for (const [m, cnt] of types) { const nxt = new Map();
    for (const key of layer.keys()) { const [pm, dv, sx] = JSON.parse(key);
      for (let x = 0; x <= cnt && sx + x <= xs; x++) { let pm2 = pm; if (x & 1) for (const i of parIdx) if (m >> i & 1) pm2 ^= 1 << i;
        const dv2 = dv.map((d, q) => d + ((m >> intIdx[q] & 1) ? x : 0)); if (dv2.some((d, q) => d > cons[intIdx[q]])) continue;
        const k2 = JSON.stringify([pm2, dv2, sx + x]); if (!nxt.has(k2)) nxt.set(k2, [key, x]); } }
    layer = nxt; layers.push(layer); }
  let tpm = 0; for (const i of parIdx) if (cons[i] === 'odd') tpm |= 1 << i;
  let key = JSON.stringify([tpm, intIdx.map(i => cons[i]), xs]); if (!layer.has(key)) return null;
  const xsol = []; for (let j = types.length; j >= 1; j--) { const [pk, x] = layers[j].get(key); xsol[j - 1] = x; key = pk; } return xsol;
}
let leaves = 0, found = 0; const witnesses = [];
for (const H of heavies.values()) {
  const deg = new Array(7).fill(0); for (const m of H) for (let i = 0; i < 7; i++) if (m >> i & 1) deg[i]++;
  if (deg.some((d, i) => d > s[i])) continue;
  const r = deg.map((d, i) => s[i] - d); const nT = n - H.length;
  if (nT < 0 || r.reduce((a, b) => a + b, 0) !== 3 * nT) continue;
  const allowed = triples.filter(t => H.every(h => (h & t) !== 0));
  const mult = new Array(allowed.length).fill(0); const posMasks = [];
  (function dfs(j, left) {
    if (witnesses.length >= maxWit) return;
    if (left === 0) { if (r.some(v => v !== 0)) return; leaves++;
      const types = H.reduce((acc, m) => { const e = acc.find(q => q[0] === m); if (e) e[1]++; else acc.push([m, 1]); return acc; }, []);
      allowed.forEach((t, q) => { if (mult[q] > 0) types.push([t, mult[q]]); });
      const xsol = splitSolve(types); if (xsol) { found++; witnesses.push({ types, x: xsol }); } return; }
    if (j === allowed.length) return;
    { let av = 0; const capT = new Array(7).fill(0);
      for (let jj = j; jj < allowed.length; jj++) { const tt = allowed[jj]; if (posMasks.every(p => (p & tt) !== 0)) { av |= tt; let cp = left; for (let i = 0; i < 7; i++) if (tt >> i & 1) cp = Math.min(cp, r[i]); for (let i = 0; i < 7; i++) if (tt >> i & 1) capT[i] += cp; } }
      for (let i = 0; i < 7; i++) if (r[i] > 0 && (!(av >> i & 1) || capT[i] < r[i])) return; }
    const t = allowed[j]; let cap = left; for (let i = 0; i < 7; i++) if (t >> i & 1) cap = Math.min(cap, r[i]);
    if (posMasks.some(p => (p & t) === 0)) cap = 0;
    for (let mlt = cap; mlt >= 0; mlt--) { mult[j] = mlt; for (let i = 0; i < 7; i++) if (t >> i & 1) r[i] -= mlt; if (mlt > 0) posMasks.push(t);
      dfs(j + 1, left - mlt); if (mlt > 0) posMasks.pop(); for (let i = 0; i < 7; i++) if (t >> i & 1) r[i] += mlt; mult[j] = 0; }
  })(0, nT);
  if (witnesses.length >= maxWit) break;
}
console.log(`degree-feasible leaves: ${leaves}; split-feasible: ${found}${witnesses.length >= maxWit ? ' (stopped at maxWit)' : ''}`);
// explicit witnesses + independent check: points 0..xs-1 are X
for (const w of witnesses) {
  const pts = []; w.types.forEach(([m, cnt], j) => { for (let a = 0; a < cnt; a++) pts.push({ m, inX: a < w.x[j] }); });
  pts.sort((a, b) => (b.inX - a.inX));
  const K = Array.from({ length: 7 }, (_, i) => pts.map((p, idx) => (p.m >> i & 1) ? idx : -1).filter(v => v >= 0));
  let ok = pts.length === n && pts.filter(p => p.inX).length === xs;
  for (let a = 0; a < n; a++) for (let b = a; b < n; b++) if (!K.some(S => S.includes(a) && S.includes(b))) ok = false;
  K.forEach((S, i) => { const kx = S.filter(v => v < xs).length; if (S.length !== s[i]) ok = false;
    const c = cons[i]; if (c === 'odd' && kx % 2 !== 1) ok = false; if (c === 'even' && kx % 2 !== 0) ok = false; if (typeof c === 'number' && kx !== c) ok = false; });
  console.log('WITNESS', JSON.stringify(K), 'checked', ok, '| types', w.types.map(([m, c], j) => `${m.toString(2).padStart(7, '0')}:${c}:${w.x[j]}`).join(' '));
}
console.log(found ? 'RESULT: good seven EXISTS' : 'RESULT: NO good seven [computed exact, exhaustive]');
