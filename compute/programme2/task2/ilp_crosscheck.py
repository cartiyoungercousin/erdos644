"""Independent cross-check (different language, different method): tau by ILP (scipy.milp/HiGHS) over the explicit
member list, rho by enumeration of all subsets in increasing size. Checks engine_b/tables outputs."""
from itertools import combinations
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
def members(h, s, k):
    return [x for x in combinations(range(len(h)), k) if _sum(h, x) == s]
def _sum(h, x):
    v = 0
    for i in x: v ^= h[i]
    return v
def tau(h, s, k):
    H = members(h, s, k); n = len(h)
    A = np.zeros((len(H), n))
    for r_, x in enumerate(H): A[r_, list(x)] = 1
    res = milp(c=np.ones(n), constraints=LinearConstraint(A, lb=1), integrality=np.ones(n), bounds=Bounds(0, 1))
    return round(res.fun), len(H)
def rho(h, s):
    for w in range(1, len(h)+1):
        if any(_sum(h, x) == s for x in combinations(range(len(h)), w)): return w
cases = [([0,0,2,2,2,4,4,4,7,7,7], 1, 9, (2, 1, 3)),
         ([2,2,2,4,4,4,8,8,8,15,15], 1, 8, (2, 2, 4)),
         ([2,2,2,2,2,2,3,3,3,3,3,3], 1, 6, (6, 1, 2)),
         ([0,0,2,2,2,2,2,3,3,3,3,3], 1, 6, (5, 2, 2)),
         ([0,2,2,2,4,4,4,7,7,7], 1, 5, (3, 3, 3))]
for h, s, k, (t0, r0, p0) in cases:
    t, m = tau(h, s, k); n = len(h); r = n - k - t + 1; p = rho(h, s)
    print(h, 'k=%d members=%d tau=%d r=%d rho=%d' % (k, m, t, r, p), 'MATCH' if (t, r, p) == (t0, r0, p0) else 'MISMATCH')
