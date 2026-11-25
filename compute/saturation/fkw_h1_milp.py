r"""SATURATION Task 1(a), greedy step: the FKW family at m = 3 after shrinking ALL loose incidences.
H  = FKW: V = X + Y, |X| = 12, |Y| = 10, edges = 12-sets A with |A & X| odd (j = |A & X| in {3,5,7,9,11}).
Loose class [computed exact, spectrum_gen.js e = 1]: (z, A) with j = 11 and z the unique Y-point of A.
Shrinking A = (X - x) + y to X - x makes the other nine edges (X - x) + y' supersets; a minimal counterexample is a
clutter (deleting a superset keeps tau and (7,2)), so they are deleted.  Result:
  H1 = {edges with j in {3,5,7,9}}  +  {X - x : x in X}            (12 new 11-edges replace 120 edges)
co-edges: the "regular" 10-sets K with |K & X| odd in {3,5,7,9}, and the 12 "shrunk" co-edges Y + {x}.
tau(H1) >= tau(H) = 10 (every edge of H contains an edge of H1). This script decides whether H1 is (7,2):
a good seven of H1 with r >= 1 shrunk members Y + x_1..Y + x_r (distinct; repeats are useless) and R = 7 - r regular
members [solver-only, HiGHS MILP; any feasible point is re-checked by plain code].  r = 0 is FKW itself (no good seven,
CORE 110.3 [computed exact]).  Model (co-types J over the R regular members only; the shrunk members are explicit):
  Y-Y pairs: covered by any shrunk member.   Y - x_i: covered by Y + x_i.   x_i - x_l: need J(x_i) & J(x_l) != {}.
  X0 = X - {x_1..x_r}: every u in X0 needs J(u) & J(v) != {} for every v != u, and J(u) != {}.
Regular members: size 10, |K & X| odd (allowed down to 1: such a K is inside some Y + x, so it is dominated and a seven
using it upgrades to one with more shrunk members -- harmless since every r is run).
Usage: py -3.14 fkw_h1_milp.py"""
import itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
nX, nY, c = 12, 10, 10
for r in range(1, 8):
    R = 7 - r
    if R == 0:
        print(f"r={r}: no regular member, pairs x_i - x_l (i != l) uncovered -> NO [proved by hand]"); continue
    J = list(range(1 << R))
    idx = {}
    def var(k):
        idx[k] = len(idx)
    for j in J:
        for p in ('cY', 'cX', 'sY', 'sX'): var((p, j))
        for i in range(r): var(('t', i, j))
    for b in range(R): var(('q', b))
    nv = len(idx); A, lo, hi = [], [], []
    def row(co, l, h):
        a = np.zeros(nv)
        for k, v in co: a[idx[k]] += v
        A.append(a); lo.append(l); hi.append(h)
    INF = np.inf
    nX0 = nX - r
    for j in J:
        row([(('cY', j), 1), (('sY', j), -nY)], -INF, 0); row([(('cY', j), 1), (('sY', j), -1)], 0, INF)
        row([(('cX', j), 1), (('sX', j), -nX0)], -INF, 0); row([(('cX', j), 1), (('sX', j), -1)], 0, INF)
    row([(('sX', 0), 1)], 0, 0)  # X0 points need J != {}
    row([(('cY', j), 1) for j in J], nY, nY); row([(('cX', j), 1) for j in J], nX0, nX0)
    for i in range(r): row([(('t', i, j), 1) for j in J], 1, 1)
    for j1, j2 in itertools.product(J, J):
        if j1 & j2: continue
        if j1 < j2: row([(('sX', j1), 1), (('sX', j2), 1)], -INF, 1)
        row([(('sX', j1), 1), (('sY', j2), 1)], -INF, 1)
        for i in range(r):
            row([(('sX', j1), 1), (('t', i, j2), 1)], -INF, 1)
            for l in range(i + 1, r): row([(('t', i, j1), 1), (('t', l, j2), 1)], -INF, 1)
    for b in range(R):
        inb = [j for j in J if j >> b & 1]
        row([(('cY', j), 1) for j in inb] + [(('cX', j), 1) for j in inb] + [(('t', i, j), 1) for j in inb for i in range(r)], c, c)
        row([(('cX', j), 1) for j in inb] + [(('t', i, j), 1) for j in inb for i in range(r)] + [(('q', b), -2)], 1, 1)
    lb = np.zeros(nv); ub = np.zeros(nv); ig = np.ones(nv)
    for k, j in idx.items():
        ub[j] = {'cY': nY, 'cX': nX0, 'sY': 1, 'sX': 1, 't': 1, 'q': 6}[k[0]]
    res = milp(np.zeros(nv), constraints=LinearConstraint(np.array(A), lo, hi), integrality=ig, bounds=Bounds(lb, ub),
               options={'time_limit': 3600})
    if res.x is None:
        print(f"r={r}: status {res.status}: {res.message} -> " + ("NO good seven [solver-only]" if res.status == 2 else "UNDECIDED")); continue
    x = np.round(res.x).astype(int)
    pts = []  # (inX, regular co-type, shrunk index or None)
    for j in J:
        pts += [('Y', j, None)] * x[idx[('cY', j)]] + [('X0', j, None)] * x[idx[('cX', j)]]
    for i in range(r):
        pts += [('x', [j for j in J if x[idx[('t', i, j)]]][0], i)]
    members = [{p for p, (_, j, _) in enumerate(pts) if j >> b & 1} for b in range(R)]
    members += [{p for p, (k, _, s) in enumerate(pts) if k == 'Y' or s == i} for i in range(r)]
    Xp = {p for p, (k, _, _) in enumerate(pts) if k != 'Y'}
    ok = len(pts) == 22 and all(len(M) == 10 and len(M & Xp) % 2 for M in members[:R])
    ok &= all(any(u in M and v in M for M in members) for u in range(22) for v in range(u, 22))
    print(f"r={r}: good seven FOUND, plain-code re-check {ok}; regular |K & X| = {[len(M & Xp) for M in members[:R]]}")
