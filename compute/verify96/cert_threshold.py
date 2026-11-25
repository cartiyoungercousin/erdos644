r"""Independent check of CORE Theorem 96.1 (notes/verify/thm96_1.md).  [computed float, MILP on scipy/HiGHS]
For r members (mass c = N-1 each) and 7-r requests (mass <= t): maximise y = mass of points whose co-type contains [r]
(the core Y inside every member), subject to an eta-cell of points (x_0) whose co-type avoids [r], and the co-types in use
(positive mass) forming an intersecting family on [7] (z_J + z_J' <= 1 for disjoint J, J'; z_empty = 0).
Written from the definitions in CORE 96 only (does not reuse compute/strip/window_density.py).
Usage: py -3.14 cert_threshold.py"""
import itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix, csr_matrix
SUB = list(range(128)); R7 = range(7)
def ystar(N, t, r, eta):
    c = N - 1; full_r = (1 << r) - 1
    A_ok = [J for J in SUB if J and not (J & full_r)]           # x0-cell co-types
    B_ok = [J for J in SUB if J and (J & full_r) == full_r]     # Y co-types
    G_ok = [J for J in SUB if J]
    var = [("a", J) for J in A_ok] + [("b", J) for J in B_ok] + [("g", J) for J in G_ok] + [("z", J) for J in G_ok]
    ix = {v: i for i, v in enumerate(var)}; nv = len(var)
    rows = []; lo = []; hi = []
    def add(coef, l, h): rows.append(coef); lo.append(l); hi.append(h)
    mass = lambda J: [(ix[(s, J)], 1) for s in "abg" if (s, J) in ix]
    for i in R7:
        coef = [p for J in G_ok if J >> i & 1 for p in mass(J)]
        if i < r: add(coef, c, c)
        else: add(coef, 0, t)
    add([(ix[("a", J)], 1) for J in A_ok], eta, eta)
    add([p for J in G_ok for p in mass(J)], N, N)
    for J in G_ok: add(mass(J) + [(ix[("z", J)], -N)], -np.inf, 0)
    for J, J2 in itertools.combinations(G_ok, 2):
        if not J & J2: add([(ix[("z", J)], 1), (ix[("z", J2)], 1)], -np.inf, 1)
    A = lil_matrix((len(rows), nv))
    for k, coef in enumerate(rows):
        for i, v in coef: A[k, i] += v
    cost = np.zeros(nv)
    for J in B_ok: cost[ix[("b", J)]] = -1
    integ = np.array([1 if s == "z" else 0 for s, _ in var])
    ub = np.array([1 if s == "z" else N for s, _ in var], float)
    res = milp(cost, constraints=LinearConstraint(csr_matrix(A), lo, hi), integrality=integ, bounds=Bounds(0, ub),
               options={"time_limit": 300})
    return None if res.status not in (0,) or res.x is None else -res.fun
eta = 0.002
print("eta (x0 cell) =", eta)
for eps in (0.0021, 0.01, 0.03):
    t = 0.75 + eps
    for N in (5 * t - 2 + 0.01, 1.85, 1.95, 2.05, 2.15, 3 - t - 0.005):
        if not (5 * t - 2 < N < 3 - t): continue
        d = N - 1.75; pred = (d + 3 * eps) / 2
        out = []
        for r in range(0, 8):
            ys = ystar(N, t, r, eta); out.append("inf" if ys is None else f"{ys:.4f}")
        print(f"eps={eps} t={t:.4f} N={N:.4f} delta={d:.4f}: (delta+3eps)/2={pred:.4f}  4eps={4*eps:.4f}  y*(r) r=0..7: {out}", flush=True)
