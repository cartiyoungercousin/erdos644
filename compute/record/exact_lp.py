"""Exact (Fraction) feasibility for standard-form systems   M y = r,  y >= 0   (two-phase simplex,
Bland's rule).  Used by the SEARCH to turn floating-point duals into exact certificates; the
independent checker (check.py) never solves an LP, it only multiplies certificates out."""
from fractions import Fraction as Fr


def feasible_std(M, r, cols=None):
    """M: list of q rows (lists of length m, Fractions), r: q Fractions.  Returns y (list of m
    Fractions) with M y = r, y >= 0, or None.  cols: restrict the support to these columns."""
    q = len(M); m = len(M[0]) if q else 0
    cols = list(range(m)) if cols is None else list(cols)
    nc = len(cols)
    T = []
    for i in range(q):
        rowv = [M[i][j] for j in cols]; rhs = r[i]
        if rhs < 0: rowv = [-v for v in rowv]; rhs = -rhs
        art = [Fr(0)] * q; art[i] = Fr(1)
        T.append(rowv + art + [rhs])
    basis = [nc + i for i in range(q)]
    W = nc + q
    cost = [Fr(0)] * (W + 1)
    for i in range(q):
        for j in range(W + 1): cost[j] -= T[i][j]
    for j in range(nc, nc + q): cost[j] += 1
    # reduced cost of artificials = 0 (they are basic)
    for j in range(nc, nc + q): cost[j] = Fr(0)
    it = 0
    while True:
        it += 1
        if it > 5000: return None
        enter = next((j for j in range(W) if cost[j] < 0), None)
        if enter is None: break
        best = None
        for i in range(q):
            if T[i][enter] > 0:
                ratio = T[i][W] / T[i][enter]
                if best is None or ratio < best[0] or (ratio == best[0] and basis[i] < basis[best[1]]):
                    best = (ratio, i)
        if best is None: return None
        i = best[1]; p = T[i][enter]
        T[i] = [v / p for v in T[i]]
        for k in range(q):
            if k != i and T[k][enter] != 0:
                f = T[k][enter]; T[k] = [a - f * c for a, c in zip(T[k], T[i])]
        f = cost[enter]; cost = [a - f * c for a, c in zip(cost, T[i])]
        basis[i] = enter
    if cost[W] != 0: return None          # -(sum of artificials) at optimum
    y = [Fr(0)] * m
    for i in range(q):
        if basis[i] < nc: y[cols[basis[i]]] = T[i][W]
        elif T[i][W] != 0: return None
    return y
