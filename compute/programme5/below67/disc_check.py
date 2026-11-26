"""Discard finishes at a class-A spoiled state: for every grid R2 (live types, maximal) take his keep-all-best answer L*
(fast2.adv_best) and compute her best finish over ALL kept subsets (engine.best_finish: keep 5 + 2 blocks, keep 4 + 3,
keep 3 + 4; exact MILP).  min over R2 of that value > t  =>  discards do not rescue her at this state.
usage: py -3.14 disc_check.py delta R1(5 comma) excl(E,F,G comma) h"""
import sys, itertools, numpy as np
import fast2, depth2, engine
from run_A import leaf_discards
EPS = 1e-9; K14 = 14.0
delta = float(sys.argv[1]); R = tuple(map(float, sys.argv[2].split(','))); ex = list(map(float, sys.argv[3].split(','))); h = float(sys.argv[4])
t = 12 - delta; tn = t / K14; C = depth2.cells(6, 5)
e = {'X': 0.0, 'Y': 0.0, 'E': ex[0], 'F': ex[1], 'G': ex[2]}
P = depth2.pos4(C, R, e)
live = P.live; m = np.array([P.types[ty] for ty in live]); n = len(live)
pos = [i for i in range(n) if m[i] > EPS]; zero = [i for i in range(n) if m[i] <= EPS]
worst = (np.inf, None); cnt = 0
for rv in itertools.product(*[fast2.grid_vals(m[i], h / K14) for i in pos]):
    s = sum(rv)
    if s > tn + EPS or (s + h / K14 <= tn + EPS and s < m.sum() - EPS): continue
    r = np.zeros(n); r[pos] = rv
    fs = frozenset([live[i] for i in zero] + [live[i] for i in pos if abs(r[i] - m[i]) <= EPS])
    verts, F = P.graph(fs)
    v, Lin = fast2.adv_best(F, verts, live, m, r)
    d, S = leaf_discards(C, R, e, r, Lin, P)
    val = min(v, d); cnt += 1
    if val < worst[0]: worst = (val, (np.round(r * K14, 3), v * K14, d * K14, S))
print('state R1=%s excl=%s t=%g/14: %d R2 checked; min over R2 of min(keep-all, discards) = %.4f/14 at %s' % (R, ex, t, cnt, worst[0] * K14, worst[1]))
