// CORE 110: exact (7,2) check of parity / complete families by co-type (spectrum) enumeration. [computed exact]
// Family on n points, co-edges = (n-k)-sets; parity mode: co-edges K with |K ∩ X| ≡ (|X| - 1) mod 2, i.e. |A ∩ X| odd
// for the edge A = V \ K (|X| = xs).  A bad 7-tuple (= good seven of co-edges) <=> nonneg integers x_I, y_I (I ⊆ [7],
// co-type multiplicities on X and on Y) with: support pairwise intersecting, Σx = xs, Σy = n - xs,
// deg_i(x + y) = c := n - k, and (parity mode) deg_i(x) ≡ xs - 1 (mod 2)  [|K_i ∩ X| = xs - |A_i ∩ X|].
// Hand facts used: |I| = 1 or 2 is impossible when 2c < n (K_i, resp. K_i ∪ K_j, would be V); hence all |I| >= 3 and
// Σ_x (|I_x| - 3) = 7c - 3n =: E. Heavy co-types (|I| >= 4) carry excess exactly E.
// Method: enumerate heavy multisets up to S_7, then DFS over triple multiplicities (intersecting support, exact degrees),
// then an exact DP over the X/Y split. Exhaustive. Usage: node fkw_spectrum.js n k xs   (xs = 0: complete family)
const [n, k, xs] = process.argv.slice(2).map(Number);
const c = n - k, E = 7 * c - 3 * n, parity = xs > 0, NX = parity ? xs : 0;
const pc = m => { let s = 0; while (m) { m &= m - 1; s++; } return s; };
if (!(2 * c < n)) throw new Error('needs 2c < n');
console.log(`n=${n} k=${k} |X|=${xs} c=${c} excess E=${E}`);
if (E < 0) { console.log('E < 0: NO bad 7-tuple (exact, by the count)'); process.exit(0); }
// permutations of [7]
const perms = []; (function gen(a, used) { if (a.length === 7) { perms.push(a.slice()); return; } for (let i = 0; i < 7; i++) if (!used[i]) { used[i] = 1; a.push(i); gen(a, used); a.pop(); used[i] = 0; } })([], []);
const ptab = perms.map(p => { const t = new Uint8Array(128); for (let m = 0; m < 128; m++) { let r = 0; for (let i = 0; i < 7; i++) if (m >> i & 1) r |= 1 << p[i]; t[m] = r; } return t; });
const heavyMasks = []; for (let m = 0; m < 128; m++) if (pc(m) >= 4) heavyMasks.push(m);
// heavy multisets with excess E (nondecreasing index order), pairwise intersecting
const heavies = new Map();
(function gen(start, ex, cur) {
  if (ex === E) {
    let best = null;
    for (const t of ptab) { const s = cur.map(m => t[m]).sort((a, b) => a - b); const key = s.join(','); if (best === null || key < best) best = key; }
    if (!heavies.has(best)) heavies.set(best, best === '' ? [] : best.split(',').map(Number));
    return;
  }
  for (let j = start; j < heavyMasks.length; j++) { const m = heavyMasks[j], e = pc(m) - 3; if (ex + e > E) continue;
    if (cur.some(q => (q & m) === 0)) continue; cur.push(m); gen(j, ex + e, cur); cur.pop(); }
})(0, 0, []);
console.log(`heavy multisets up to S7: ${heavies.size}`);
const triples = []; for (let m = 0; m < 128; m++) if (pc(m) === 3) triples.push(m);
let leaves = 0, found = 0;
function splitOK(types) { // types: [mask, count]; exists x_I in [0,count] with Σx = NX and deg_i(x) odd-target
  if (!parity) return { ok: true };
  const target = ((NX - 1) & 1) ? 127 : 0; // deg_i(x) ≡ NX - 1
  // mask -> bitset (Number, NX + 1 <= 30 bits) of achievable sums
  let cur = new Int32Array(128); cur[0] = 1; const lim = (1 << (NX + 1)) - 1;
  for (const [m, cnt] of types) {
    const nxt = new Int32Array(128);
    for (let s = 0; s < 128; s++) if (cur[s]) for (let x = 0; x <= Math.min(cnt, NX); x++) { const t = (x & 1) ? s ^ m : s; nxt[t] |= (cur[s] << x) & lim; }
    cur = nxt;
  }
  return { ok: ((cur[target] >> NX) & 1) === 1 };
}
function reconstruct(types) { // find explicit x by backtracking DP (only for printing witnesses)
  const target = ((NX - 1) & 1) ? 127 : 0;
  const layers = [new Array(128).fill(0n)]; layers[0][0] = 1n; const lim = (1n << BigInt(NX + 1)) - 1n;
  for (const [m, cnt] of types) { const cur = layers[layers.length - 1], nxt = new Array(128).fill(0n);
    for (let s = 0; s < 128; s++) if (cur[s]) for (let x = 0; x <= Math.min(cnt, NX); x++) { const t = (x & 1) ? s ^ m : s; nxt[t] |= (cur[s] << BigInt(x)) & lim; } layers.push(nxt); }
  const xsol = []; let s = target, sum = NX;
  for (let j = types.length - 1; j >= 0; j--) { const [m, cnt] = types[j];
    for (let x = 0; x <= Math.min(cnt, sum); x++) { const p = (x & 1) ? s ^ m : s; if ((layers[j][p] >> BigInt(sum - x)) & 1n) { xsol[j] = x; s = p; sum -= x; break; } } }
  return xsol;
}
const witnesses = [];
let hdone = 0;
for (const H of heavies.values()) {
  if (++hdone % 5 === 0) console.log(`  heavy ${hdone}/${heavies.size}, leaves so far ${leaves}`);
  const deg = new Array(7).fill(0); for (const m of H) for (let i = 0; i < 7; i++) if (m >> i & 1) deg[i]++;
  if (deg.some(d => d > c)) continue;
  const need = deg.map(d => c - d); const nT = n - H.length;
  const allowed = triples.filter(t => H.every(h => (h & t) !== 0));
  const mult = new Array(allowed.length).fill(0);
  // suffix availability per element
  const suf = []; for (let j = allowed.length; j >= 0; j--) { const a = new Array(7).fill(0); if (j < allowed.length) { for (let i = 0; i < 7; i++) a[i] = suf[0][i] + (allowed[j] >> i & 1); } suf.unshift(a); }
  const r = need.slice(); let posMasks = [];
  (function dfs(j, left) {
    if (found && witnesses.length >= 3) return;
    if (left === 0) { if (r.some(v => v !== 0)) return; leaves++;
      const types = H.reduce((acc, m) => { const e = acc.find(q => q[0] === m); if (e) e[1]++; else acc.push([m, 1]); return acc; }, []);
      allowed.forEach((t, q) => { if (mult[q] > 0) types.push([t, mult[q]]); });
      if (splitOK(types).ok) { found++; if (witnesses.length < 3) witnesses.push({ types, x: reconstruct(types) }); }
      return; }
    if (j === allowed.length) return;
    for (let i = 0; i < 7; i++) if (r[i] > 0 && suf[j][i] === 0) return;
    // dynamic availability: later triples compatible with every positive triple so far must cover all unmet elements
    { let av = 0; const capT = new Array(7).fill(0);
      for (let jj = j; jj < allowed.length; jj++) { const tt = allowed[jj]; if (posMasks.every(p => (p & tt) !== 0)) { av |= tt; let cp = left; for (let i = 0; i < 7; i++) if (tt >> i & 1) cp = Math.min(cp, r[i]); for (let i = 0; i < 7; i++) if (tt >> i & 1) capT[i] += cp; } }
      for (let i = 0; i < 7; i++) if (r[i] > 0 && (!(av >> i & 1) || capT[i] < r[i])) return; }
    const t = allowed[j]; let cap = left; for (let i = 0; i < 7; i++) if (t >> i & 1) cap = Math.min(cap, r[i]);
    if (posMasks.some(p => (p & t) === 0)) cap = 0;
    for (let mlt = cap; mlt >= 0; mlt--) {
      mult[j] = mlt; for (let i = 0; i < 7; i++) if (t >> i & 1) r[i] -= mlt;
      if (mlt > 0) posMasks.push(t);
      dfs(j + 1, left - mlt);
      if (mlt > 0) posMasks.pop();
      for (let i = 0; i < 7; i++) if (t >> i & 1) r[i] += mlt; mult[j] = 0;
    }
  })(0, nT);
}
console.log(`degree-feasible co-type multisets (leaves): ${leaves}; split-feasible: ${found}`);
if (!found) console.log('RESULT: NO bad 7-tuple (no good seven of co-edges) [computed exact, exhaustive]');
else {
  console.log('RESULT: bad 7-tuple EXISTS; witnesses (co-type mask : total count : on X)');
  // explicit construction and independent pair check
  for (const w of witnesses) {
    const pts = []; w.types.forEach(([m, cnt], j) => { const xx = parity ? w.x[j] : 0; for (let a = 0; a < cnt; a++) pts.push({ m, inX: a < xx }); });
    const K = Array.from({ length: 7 }, (_, i) => pts.map((p, idx) => (p.m >> i & 1) ? idx : -1).filter(v => v >= 0));
    let okPairs = true; for (let a = 0; a < pts.length; a++) for (let b = a + 1; b < pts.length; b++) if ((pts[a].m & pts[b].m) === 0) okPairs = false;
    const sizes = K.map(s => s.length), xpar = K.map(s => s.filter(v => pts[v].inX).length);
    console.log('  ', w.types.map(([m, cnt], j) => `${m.toString(2).padStart(7, '0')}:${cnt}:${parity ? w.x[j] : '-'}`).join(' '),
      `| sizes ${sizes} |K∩X| ${xpar} pairs-covered ${okPairs} nX=${pts.filter(p => p.inX).length}`);
  }
}
