r"""Exact tools for two-block profile families (PROGRAMME2_C.md).
V = X u Y, |X| = a, |Y| = b, n = a + b.  H_J = all k-sets B with |B n X| in J.
- tau(H_J) = n - (largest hole), a hole profile (x, y) being one with J n [k-y, x] empty (exact, by enumeration).
- Fano-type good seven <=> integers x_p, y_p >= 0 (p = 0..6) summing to a, b with, for every line l,
  J n [k - Y_l, X_l] nonempty, where X_l = sum_{p not in l} x_p (exact ILP, HiGHS via scipy.milp).
- coset bias: H_J's fraction in the best half-space {u.x = c} over ALL functionals u (by symmetry u is determined
  by t = |u n X|, s = |u n Y|; bias = sum_j K_j(t;a) K_{k-j}(s;b) / |H|, Krawtchouk, exact integers)."""
import sys, itertools
from math import comb
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

LINES = [(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
AF = [[p for p in range(7) if p not in L] for L in LINES]     # anti-flags R_l

def tau(J, a, b, k):
    Js = set(J); best = -1
    for x in range(a + 1):
        for y in range(b + 1):
            if not any(max(0, k - y) <= j <= x for j in Js):
                best = max(best, x + y)
    return a + b - best

def seven(J, a, b, k, timelimit=60):
    """Return (x, y) class sizes of a Fano-type good seven, or None (exact: ILP optimal/infeasible)."""
    J = sorted(set(j for j in J if 0 <= j <= min(a, k) and k - j <= b))
    if not J: return None
    nJ = len(J); nv = 14 + 7 * nJ          # x_0..6, y_0..6, z_{l,j}
    A = []; lo = []; hi = []
    row = np.zeros(nv); row[0:7] = 1; A.append(row); lo.append(a); hi.append(a)
    row = np.zeros(nv); row[7:14] = 1; A.append(row); lo.append(b); hi.append(b)
    for l in range(7):
        zs = [14 + l * nJ + i for i in range(nJ)]
        row = np.zeros(nv); row[zs] = 1; A.append(row); lo.append(1); hi.append(1)
        # sum j z <= X_l
        row = np.zeros(nv)
        for i, j in enumerate(J): row[zs[i]] = j
        for p in AF[l]: row[p] -= 1
        A.append(row); lo.append(-np.inf); hi.append(0)
        # k - Y_l <= sum j z   <=>  -sum j z - Y_l <= -k
        row = np.zeros(nv)
        for i, j in enumerate(J): row[zs[i]] = -j
        for p in AF[l]: row[7 + p] -= 1
        A.append(row); lo.append(-np.inf); hi.append(-k)
    ub = np.array([a] * 7 + [b] * 7 + [1] * (7 * nJ), float)
    res = milp(np.zeros(nv), constraints=LinearConstraint(np.array(A), lo, hi),
               integrality=np.ones(nv), bounds=Bounds(np.zeros(nv), ub), options={'time_limit': timelimit})
    if res.status == 0:
        v = np.round(res.x).astype(int); return list(v[:7]), list(v[7:14])
    if res.status == 2: return None
    raise RuntimeError(f'ILP status {res.status} {res.message}')

def kraw(j, t, n):
    return sum((-1) ** i * comb(t, i) * comb(n - t, j - i) for i in range(j + 1))

def best_halfspace(J, a, b, k):
    """max over nontrivial functionals of the fraction of H in the majority side; returns (frac, t, s)."""
    J = [j for j in J if 0 <= j <= a and 0 <= k - j <= b]
    size = sum(comb(a, j) * comb(b, k - j) for j in J)
    best = (0.0, None, None)
    for t in range(a + 1):
        Kt = [kraw(j, t, a) for j in range(k + 1)]
        for s in range(b + 1):
            if (t, s) in ((0, 0), (a, b)): continue
            bias = sum(Kt[j] * kraw(k - j, s, b) for j in J)
            f = (1 + abs(bias) / size) / 2
            if f > best[0]: best = (f, t, s)
    return best

def verify_seven(J, a, b, k, xs, ys):
    """independent check: build explicit sets, take members inside each R_l, test no 2-point transversal."""
    X = list(range(a)); Y = list(range(a, a + b)); col = {}
    i = 0
    for p in range(7):
        for _ in range(xs[p]): col[X[i]] = p; i += 1
    i = 0
    for p in range(7):
        for _ in range(ys[p]): col[Y[i]] = p; i += 1
    Js = set(J); sev = []
    for l in range(7):
        R = [v for v in col if col[v] not in LINES[l]]
        RX = [v for v in R if v < a]; RY = [v for v in R if v >= a]
        j = next(j for j in sorted(Js) if j <= len(RX) and k - j <= len(RY) and k - j >= 0)
        sev.append(set(RX[:j] + RY[:k - j]))
    V = range(a + b)
    for u in V:
        for w in V:
            if all(u in B or w in B for B in sev): return False
    return all(len(B) == k for B in sev)

if __name__ == '__main__':
    # sanity: FKW m=2,3 (no seven), FKW at 7m+2 (seven), K_13^(8) (no seven), K_14^(8) (seven)
    for m in (2, 3):
        k = 4 * m; a = k
        for n in (7 * m + 1, 7 * m + 2):
            J = range(1, k + 1, 2); r = seven(J, a, n - a, k)
            print('FKW m', m, 'n', n, 'tau', tau(J, a, n - a, k), 'seven', r,
                  'verified' if r and verify_seven(J, a, n - a, k, *r) else '')
    for n in (13, 14):
        J = range(0, 9); print('K', n, 8, 'tau', tau(J, 5, n - 5, 8), 'seven', seven(J, 5, n - 5, 8))
    print('H1', tau([3,5,7,9], 12, 10, 12), seven([3,5,7,9], 12, 10, 12))
