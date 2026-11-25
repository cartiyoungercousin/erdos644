r"""Independent exact certificate for the seam family E = {8-subsets B of W, |W| = 14, |B n W1| odd}, |W1| = |W2| = 7.
Co-edge form: a good seven = seven 6-sets (complements, repeats allowed) covering all 91 pairs of W.
Counting [hand]: a point x needs >= ceil(13/5) = 3 co-edges through it, and 7*6 = 42 = 14*3, so every point lies in
EXACTLY 3 co-edges.  Dualise: point x -> its 3-set T_x of co-edge labels in [7]; pairs covered <=> the T_x are pairwise
intersecting; label b has degree 6.  A co-edge K_b is the complement of a member iff |W1 \ K_b| is odd, i.e.
|W1 n K_b| = sum_{T ni b} a_T is even (|W1| = 7).  ILP over multiplicities a_T (points of W1 with 3-set T), b_T (W2).
Run with parity on (E) and off (complete K_14^(8), control)."""
import itertools, sys
S = [frozenset(T) for T in itertools.combinations(range(7), 3)]
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
def solve(parity, w1=7, w2=7):
    # variables: a_T (35), b_T (35), u_T (35), z_lab (7)
    nT = len(S); N = 3 * nT + 7; A = []; lo = []; hi = []
    def row(d, l, h):
        r = np.zeros(N); [r.__setitem__(i, v) for i, v in d.items()]; A.append(r); lo.append(l); hi.append(h)
    row({i: 1 for i in range(nT)}, w1, w1); row({nT + i: 1 for i in range(nT)}, w2, w2)
    for i in range(nT): row({i: 1, nT + i: 1, 2 * nT + i: -14}, -np.inf, 0)
    for i, j in itertools.combinations(range(nT), 2):
        if not (S[i] & S[j]): row({2 * nT + i: 1, 2 * nT + j: 1}, -np.inf, 1)
    for lab in range(7):
        d = {}
        for i, T in enumerate(S):
            if lab in T: d[i] = 1; d[nT + i] = 1
        row(d, 6, 6)
        if parity:
            d = {i: 1 for i, T in enumerate(S) if lab in T}; d[3 * nT + lab] = -2; row(d, 0, 0)
    ub = np.array([w1] * nT + [w2] * nT + [1] * nT + [7] * 7, float)
    r = milp(np.zeros(N), constraints=LinearConstraint(np.array(A), lo, hi), integrality=np.ones(N),
             bounds=Bounds(np.zeros(N), ub))
    if r.status != 0: return ('INFEASIBLE' if r.status == 2 else f'status {r.status}'), None
    x = np.round(r.x).astype(int)
    return 'FEASIBLE', {''.join(map(str, sorted(T))): (x[i], x[nT + i]) for i, T in enumerate(S) if x[i] + x[nT + i] > 0}
for par in (False, True):
    print('parity' if par else 'complete', *solve(par))
