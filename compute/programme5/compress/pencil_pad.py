"""Pencil padding (PROGRAMME5_COMPRESS Sec 4) on complete (7,2)-families K^(k)_n.
Greedy: every member B gets one new point z shared with two further members C, D such that {B,C,D} is a pencil
(empty common intersection), preferring partners not yet padded (load 1).  Reports the load profile, tau before/after
(CP-SAT, 1 worker), and the dominated points of the padded family (star(x) subset of star(y), x != y).
(7,2) of the padded family is automatic (enlargement).  Usage: py -3.14 pencil_pad.py k n seed"""
import sys, random, itertools
from ortools.sat.python import cp_model

def tau(members, n):
    m = cp_model.CpModel(); x = [m.NewBoolVar('x%d' % i) for i in range(n)]
    for B in members: m.AddBoolOr([x[i] for i in range(n) if B >> i & 1])
    m.Minimize(sum(x)); s = cp_model.CpSolver(); s.parameters.num_workers = 1; s.parameters.max_time_in_seconds = 600
    st = s.Solve(m); return int(s.ObjectiveValue()), st == cp_model.OPTIMAL

def main(k, n, seed):
    rng = random.Random(seed)
    H = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)]
    rng.shuffle(H); idx = {B: i for i, B in enumerate(H)}
    load = [0] * len(H); stars = []
    for i, B in enumerate(H):
        if load[i]: continue
        best = None
        for _ in range(4000):
            j, l = rng.randrange(len(H)), rng.randrange(len(H))
            if len({i, j, l}) < 3 or B & H[j] & H[l]: continue
            sc = load[j] + load[l]
            if best is None or sc < best[0]: best = (sc, j, l)
            if sc == 0: break
        _, j, l = best
        for t in (i, j, l): load[t] += 1
        stars.append((i, j, l))
    m = len(stars); N = n + m
    Hs = list(H)
    for z, (i, j, l) in enumerate(stars):
        for t in (i, j, l): Hs[t] |= 1 << (n + z)
    prof = {}
    for x in load: prof[x] = prof.get(x, 0) + 1
    t0, o0 = tau(H, n); t1, o1 = tau(Hs, N)
    star = [frozenset(b for b, B in enumerate(Hs) if B >> v & 1) for v in range(N)]
    dom = sum(1 for x in range(N) if any(y != x and star[x] <= star[y] for y in range(N)))
    print('K^(%d)_%d seed %d: |H|=%d new points=%d loads=%s tau %d%s -> %d%s on %d points; dominated points: %d'
          % (k, n, seed, len(H), m, dict(sorted(prof.items())), t0, '' if o0 else '?', t1, '' if o1 else '?', N, dom))

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))
