r"""CORE 110 cross-check: (7,2) of the FKW parity family by MILP (scipy/HiGHS), independent formulation:
all 127 nonempty co-types allowed (no hand reduction), binary support with disjoint-pair exclusion. [solver-only]
Usage: py -3.14 fkw_milp.py n k xs"""
import sys, itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
n, k, xs = map(int, sys.argv[1:4]); c = n - k; ny = n - xs
I = list(range(1, 128)); m = len(I)
# vars: x_I (m), y_I (m), z_I (m), w_i (7)
nv = 3 * m + 7; X = lambda j: j; Y = lambda j: m + j; Z = lambda j: 2 * m + j; W = lambda i: 3 * m + i
rows, lo, hi = [], [], []
def add(coef, l, h):
    r = np.zeros(nv)
    for j, v in coef: r[j] += v
    rows.append(r); lo.append(l); hi.append(h)
add([(X(j), 1) for j in range(m)], xs, xs); add([(Y(j), 1) for j in range(m)], ny, ny)
for i in range(7):
    js = [j for j, s in enumerate(I) if s >> i & 1]
    add([(X(j), 1) for j in js] + [(Y(j), 1) for j in js], c, c)
    # |K_i ∩ X| = sum x ≡ xs - 1 (mod 2):  sum x - 2 w_i = (xs - 1) % 2
    add([(X(j), 1) for j in js] + [(W(i), -2)], (xs - 1) % 2, (xs - 1) % 2)
for j in range(m):
    add([(X(j), 1), (Y(j), 1), (Z(j), -n)], -np.inf, 0)
for a, b in itertools.combinations(range(m), 2):
    if I[a] & I[b] == 0: add([(Z(a), 1), (Z(b), 1)], -np.inf, 1)
A = np.array(rows)
ub = np.array([xs] * m + [ny] * m + [1] * m + [n] * 7, float)
res = milp(c=np.zeros(nv), constraints=LinearConstraint(A, lo, hi), integrality=np.ones(nv), bounds=Bounds(np.zeros(nv), ub))
print(f"n={n} k={k} |X|={xs}: status={res.status} ({res.message})")
if res.status == 0:
    x = np.round(res.x).astype(int); pts = []
    for j, s in enumerate(I): pts += [(s, 1)] * x[X(j)] + [(s, 0)] * x[Y(j)]
    ok = all(p[0] & q[0] for p, q in itertools.combinations(pts, 2))
    sz = [sum(1 for p in pts if p[0] >> i & 1) for i in range(7)]; sx = [sum(1 for p in pts if p[0] >> i & 1 and p[1]) for i in range(7)]
    print("  bad 7-tuple found; verified:", ok, "sizes", sz, "|K∩X|", sx)
