r"""Route A, class A, level 1: is Theorem P's passive play S*-legal?  State after Theorem P's K (units k/14):
live X=6 (E,F), Y=5 (E,G), A=alpha (G,K), B=beta=14-alpha (F,K); dead E'=3 (E), Fd=8-beta (F), Gd=9-alpha (G),
Z=0+ (free), outside unlimited.  For a request R he answers M (avoids R, mass 14, traces on E,F,G,K in S*).
eff(M) = phi(X-M, A\M) + phi(Y\M, B\M), phi(u,w) = u+w if both > 0 else 0 (killed live mass that matters).
Theorem P's accounting: three kept later answers with eff <= t each cannot close (sum < 36).
Exact MILP per R (trace intervals and phi-switches binary).  R: live cells on grid h (remainder to fill t into one
live cell), dead cells requested 0 or fully.  Reports min-eff excess over t.
usage: py -3.14 level1.py alpha h delta"""
import sys, itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
al, h, de = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
be = 14 - al; t = 12 - de
SINT = [(0, 45 / 12), (60 / 12, 73 / 12), (80 / 12, 14)]          # S* (G=168) in units k/14
C = ['X', 'Y', 'A', 'B', 'Ep', 'Fd', 'Gd']
M_ = {'X': 6, 'Y': 5, 'A': al, 'B': be, 'Ep': 3, 'Fd': 8 - be, 'Gd': 9 - al}
MEM = {'E': ['X', 'Y', 'Ep'], 'F': ['X', 'B', 'Fd'], 'G': ['Y', 'A', 'Gd'], 'K': ['A', 'B']}
BIG = 40.0
def min_eff(r):
    # vars: m(7) o(1) eff(2) w(4*3) z(4: X,A,Y,B switches)
    n = 7; io = 7; ie = 8; iw = 10; iz = 22; NV = 26
    A = []; lo = []; hi = []
    def row(d, l, u):
        v = np.zeros(NV)
        for k, c in d.items(): v[k] += c
        A.append(v); lo.append(l); hi.append(u)
    row({**{i: 1 for i in range(n)}, io: 1}, 14, 14)
    for j, (mem, cs) in enumerate(MEM.items()):
        for k, (a, b) in enumerate(SINT):
            d = {C.index(c): 1 for c in cs}
            row({**{x: -y for x, y in d.items()}, iw + 3 * j + k: BIG}, -np.inf, BIG - a)   # w=1 => trace >= a
            row({**d, iw + 3 * j + k: BIG}, -np.inf, BIG + b)                              # w=1 => trace <= b
        row({iw + 3 * j + k: 1 for k in range(3)}, 1, np.inf)
    # s_c = M_c - m_c ; z_c = 1 => s_c <= 0
    for q, c in enumerate(['X', 'A', 'Y', 'B']):
        row({C.index(c): -1, iz + q: BIG}, -np.inf, BIG - M_[c])
    # eff >= sX+sA - BIG(zX+zA) ; eff >= sY+sB - BIG(zY+zB)
    row({ie: 1, C.index('X'): 1, C.index('A'): 1, iz: BIG, iz + 1: BIG}, M_['X'] + M_['A'], np.inf)
    row({ie + 1: 1, C.index("Y"): 1, C.index("B"): 1, iz + 2: BIG, iz + 3: BIG}, M_['Y'] + M_['B'], np.inf)
    ub = np.concatenate([[max(0, M_[c] - r[i]) for i, c in enumerate(C)], [14, 60, 60], np.ones(16)])
    integ = np.zeros(NV); integ[iw:] = 1
    c = np.zeros(NV); c[ie] = 1; c[ie + 1] = 1
    res = milp(c, constraints=LinearConstraint(np.array(A), lo, hi), integrality=integ, bounds=Bounds(np.zeros(NV), ub))
    return (res.fun, res.x[:8]) if res.status == 0 else (np.inf, None)
def grid(m):
    v = list(np.arange(0, m + 1e-9, h))
    if m - v[-1] > 1e-9: v.append(m)
    return v
reqs = set()
for dead in itertools.product([0, 1], repeat=3):
    dv = [M_['Ep'] * dead[0], M_['Fd'] * dead[1], M_['Gd'] * dead[2]]
    for free in range(4):
        oth = [i for i in range(4) if i != free]
        for vals in itertools.product(*[grid(M_[C[i]]) for i in oth]):
            rem = t - sum(vals) - sum(dv)
            if rem < -1e-9: continue
            r = [0.0] * 7
            for i, v in zip(oth, vals): r[i] = v
            r[free] = min(rem, M_[C[free]]); r[4:] = dv
            reqs.add(tuple(round(x, 6) for x in r))
reqs = sorted(reqs)
print('alpha=%g beta=%g t=%g (units k/14), grid %g: %d requests' % (al, be, t, h, len(reqs)), flush=True)
worst = (-np.inf, None); worst_struct = (-np.inf, None); nbad = 0; nbad_struct = 0
for r in reqs:
    v, m = min_eff(r)
    ex = v - t
    struct = r[0] >= 6 - 1e-9 or r[1] >= 5 - 1e-9          # contains all of X or all of Y
    if ex > 1e-7:
        nbad += 1; nbad_struct += struct
    if ex > worst[0]: worst = (ex, r)
    if struct and ex > worst_struct[0]: worst_struct = (ex, r)
print('max excess of min eff over t: %.4f at R(X,Y,A,B,Ep,Fd,Gd)=%s; requests with excess > 0: %d' % (worst[0], worst[1], nbad))
print('among requests containing all of X or all of Y: max excess %.4f at %s; with excess > 0: %d' % (worst_struct[0], worst_struct[1], nbad_struct))
