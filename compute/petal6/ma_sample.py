"""PETAL §41.4: dense sampling of unions of m arena classes inside the regime theta < c < 1 - 5t/9, tau >= t/2.
Reports max over samples of Phi - (tau + 8d/3) (arena form) and min of t - Phi (SL1 margin). Exact LP per sample.
usage: py ma_sample.py t m samples seed"""
import sys, numpy as np
from multiarena import atoms, evaluate
t = float(sys.argv[1]); m = int(sys.argv[2]); N = int(sys.argv[3]); rng = np.random.default_rng(int(sys.argv[4]))
theta = (6 * t - 2) / 5; cmax = 1 - 5 * t / 9; AT = atoms(m)
n = 0; worst_arena = -9; worst_margin = 9; rec = None; rec2 = None
for _ in range(N):
    b = rng.uniform(0.8, 1.4); sc = rng.uniform(0.01, 0.3)
    s = np.array([b if len(S) == m else rng.exponential(sc / m) * (rng.random() < 0.6) for S in AT]); rho = rng.random(m) * rng.uniform(0.02, 0.2)
    e = evaluate(s, rho, t, AT, m)
    if e is None or not (theta < e['c'] < cmax and e['tau'] >= t / 2): continue
    n += 1
    ga = e['phi'] - (e['tau'] + 8 * e['d'] / 3)
    if ga > worst_arena:
        worst_arena = ga; rec2 = (round(e['c'], 5), round(e['tau'], 5), round(e['d'], 5), round(e['phi'], 5), s.tolist(), rho.tolist())
    if t - e['phi'] < worst_margin: worst_margin = t - e['phi']; rec = (round(e['c'], 4), round(e['tau'], 4), round(e['d'], 4), np.round(s, 4).tolist(), np.round(rho, 4).tolist())
print('t', t, 'm', m, 'samples', N, 'in regime', n, 'max(Phi - arena form) %.6f' % worst_arena, 'min SL1 margin t - Phi %.6f' % worst_margin, rec, ' WORST_ARENA_GAP', rec2, flush=True)
