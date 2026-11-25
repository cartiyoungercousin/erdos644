"""Search her round-4 request sigma (anchors kept) minimising the worst static 3-round finish.
Float search; a returned value <= t with shared=True is a single pattern valid on every vertex of
the adversary polytope, hence (convexity of a fixed pattern's feasible set) on all of it."""
import sys, random, itertools
import numpy as np
from anchored_lp import CELLS, masses, one_adaptive_value, static4

def rand_sigma(m, t, rng):
    caps = np.array([m[c] for c in CELLS])
    for _ in range(1000):
        w = rng.dirichlet(np.ones(6) * 0.5)
        s = np.minimum(w * t, caps)
        # redistribute remainder
        for _ in range(10):
            rem = t - s.sum()
            if rem < 1e-12: break
            room = caps - s
            if room.sum() < 1e-12: break
            s = s + np.minimum(room, rem * room / room.sum())
        return dict(zip(CELLS, s))

def best_sigma(shape, t, iters=60, seed=1, shared=True):
    rng = np.random.default_rng(seed)
    m = masses(*shape)
    best = (float('inf'), None)
    cands = []
    # structured candidates: all budget on P, proportional; on P_ab ∪ Q_c pairs
    P = ['P12', 'P13', 'P23']
    tot = sum(m[c] for c in P)
    if tot > 0:
        cands.append({c: (min(m[c], t * m[c] / tot) if c in P else 0.0) for c in CELLS})
    for _ in range(iters):
        cands.append(rand_sigma(m, t, rng))
    for s in cands:
        v = one_adaptive_value(shape, s, t, shared=shared)
        if v < best[0]: best = (v, s)
    # local refinement
    v0, s0 = best
    step = 0.05
    for it in range(80):
        if s0 is None: break
        a, b = rng.choice(6, 2, replace=False)
        ca, cb = CELLS[a], CELLS[b]
        d = min(step, s0[ca], m[cb] - s0[cb])
        if d <= 1e-6: continue
        s1 = dict(s0); s1[ca] -= d; s1[cb] += d
        v1 = one_adaptive_value(shape, s1, t, shared=shared)
        if v1 < v0 - 1e-9:
            v0, s0 = v1, s1
        elif it % 20 == 19:
            step /= 2
    return v0, s0

if __name__ == '__main__':
    t = eval(sys.argv[1])
    shapes = [tuple(map(eval, a.split(','))) for a in sys.argv[2:]]
    for sh in shapes:
        v, s = best_sigma(sh, t)
        print(sh, 'N=%.4f static4=%.4f one-adaptive=%.4f' % (3 - sum(sh), static4(sh), v),
              {c: round(x, 4) for c, x in (s or {}).items()}, flush=True)
