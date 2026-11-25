r"""First-order anchored game (TWIN 13.3, Theorem B) with anchors KEPT among the seven.

Cells of V = B1 u B2 u B3 (anchors, empty triple intersection), units k = 1:
  P12, P13, P23 (in two anchors), Q1, Q2, Q3 (in one anchor).
Grid constraints (Theorem B): x in P_ab, y in B_c = P_ac u P_bc u Q_c need I_x n I_y != 0,
where I_x = set of later rounds at which x is killed (x in K_i = V \ E_i).
Static finish: every sub-cell picks kill-types (subsets of the remaining rounds); a cell may be split.
MILP: binary 'type used' per sub-cell, conflict constraints for disjoint types on constrained pairs.
Adaptive round 4: she requests sigma (cell masses, sum <= t); adversary adds omega = N-1-t
(K_4 = S_4 u additions, |K_4| = N - 1); then static rounds 5,6,7.
Monotonicity (TWIN 13.2(i)): a larger K_i only helps her.  [float, HiGHS]
"""
import itertools, sys


CELLS = ['P12', 'P13', 'P23', 'Q1', 'Q2', 'Q3']
# constrained pairs of anchor cells (unordered)
def constrained(a, b):
    if a == b: return False
    if a[0] == 'P' and b[0] == 'P': return True
    if a[0] == 'P' and b[0] == 'Q':
        return b[1] not in a[1:]          # P_ab with Q_c, c the third index
    if a[0] == 'Q' and b[0] == 'P':
        return constrained(b, a)
    return False
PAIRS = [(a, b) for a, b in itertools.combinations(CELLS, 2) if constrained(a, b)]

def masses(p12, p13, p23):
    return {'P12': p12, 'P13': p13, 'P23': p23,
            'Q1': 1 - p12 - p13, 'Q2': 1 - p12 - p23, 'Q3': 1 - p13 - p23}

def static_value(subcells, rounds, eps=1e-9, return_pattern=False, shared=None):
    """subcells: list of (cell, prior_frozenset, mass). Returns min over static plans of max load.
    shared: further subcell lists (same keys) that must use the SAME pattern u -- certifies a whole
    polytope of adversary answers from its vertices (the feasible set of a fixed pattern is convex)."""
    import numpy as np
    from scipy.optimize import milp, LinearConstraint, Bounds
    from scipy.sparse import lil_matrix
    groups = [subcells] + (shared or [])
    types = [frozenset(c) for r in range(len(rounds) + 1) for c in itertools.combinations(rounds, r)]
    keys = sorted({(c, pr) for g in groups for (c, pr, m) in g if m > eps}, key=lambda kk: (kk[0], sorted(kk[1])))
    idx = {}
    nv = 1                                   # var 0 = L
    for key in keys:
        for J in types:
            idx[('u',) + key + (J,)] = nv; nv += 1
    for gi, g in enumerate(groups):
        for si, (c, pr, m) in enumerate(g):
            if m <= eps: continue
            for J in types:
                idx[('z', gi, si, J)] = nv; nv += 1
    rows = []; lo = []; hi = []
    def add(coefs, l, h):
        rows.append(coefs); lo.append(l); hi.append(h)
    for gi, g in enumerate(groups):
        loads = {r: {} for r in rounds}
        for si, (c, pr, m) in enumerate(g):
            if m <= eps: continue
            eq = {}
            for J in types:
                zi = idx[('z', gi, si, J)]; ui = idx[('u', c, pr, J)]
                add({zi: 1.0, ui: -m}, -np.inf, 0.0)
                eq[zi] = 1.0
                for r in J: loads[r][zi] = 1.0
            add(eq, m, m)
        for r in rounds:
            d = dict(loads[r]); d[0] = -1.0
            add(d, -np.inf, 0.0)
    for i1, (c1, p1) in enumerate(keys):
        for (c2, p2) in keys[i1 + 1:]:
            if not constrained(c1, c2): continue
            for J1 in types:
                for J2 in types:
                    if not ((p1 | J1) & (p2 | J2)):
                        add({idx[('u', c1, p1, J1)]: 1.0, idx[('u', c2, p2, J2)]: 1.0}, -np.inf, 1.0)
    A = lil_matrix((len(rows), nv))
    for i, d in enumerate(rows):
        for j, v in d.items(): A[i, j] = v
    cost = np.zeros(nv); cost[0] = 1.0
    integ = np.zeros(nv)
    ub = np.full(nv, np.inf)
    for key, j in idx.items():
        if key[0] == 'u': integ[j] = 1; ub[j] = 1
    res = milp(cost, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=integ,
               bounds=Bounds(np.zeros(nv), ub), options={'time_limit': 120})
    if res.x is None:
        return (float('inf'), None) if return_pattern else float('inf')
    val = res.x[0]
    if return_pattern:
        pat = {key: [''.join(map(str, sorted(J))) for J in types if res.x[idx[('u',) + key + (J,)]] > 0.5] for key in keys}
        return val, pat
    return val

def static4(shape):
    m = masses(*shape)
    return static_value([(c, frozenset(), m[c]) for c in CELLS], [4, 5, 6, 7])

def after4(shape, y):
    """y: dict cell -> mass of the cell inside K_4."""
    m = masses(*shape)
    sub = []
    for c in CELLS:
        sub.append((c, frozenset([4]), y[c]))
        sub.append((c, frozenset(), m[c] - y[c]))
    return sub

def adversary_vertices(shape, sigma, t):
    """Vertices of {y : sigma <= y <= m, sum y = N - 1}: greedy fills in every cell order (deduped)."""
    m = masses(*shape)
    N = 3 - sum(shape)
    extra = N - 1 - sum(sigma[c] for c in CELLS)
    verts = set()
    for order in itertools.permutations(CELLS):
        y = dict(sigma); rem = extra
        for c in order:
            add = min(rem, m[c] - sigma[c]); y[c] += add; rem -= add
        if rem > 1e-9: continue
        verts.add(tuple(round(y[c], 12) for c in CELLS))
    return [dict(zip(CELLS, v)) for v in verts]

def one_adaptive_value(shape, sigma, t, shared=True):
    verts = adversary_vertices(shape, sigma, t)
    if not verts: return float('inf')
    if shared:
        subs = [after4(shape, y) for y in verts]
        return static_value(subs[0], [5, 6, 7], shared=subs[1:])
    return max(static_value(after4(shape, y), [5, 6, 7]) for y in verts)

if __name__ == '__main__':
    t = float(sys.argv[1]) if len(sys.argv) > 1 else 5 / 6
    for shape in [(0, .5, .5), (1/6, 7/24, 7/24), (0, 7/12, 5/12), (.5, .5, .5), (1/3, 1/3, 1/3)]:
        print(shape, 'N=%.3f' % (3 - sum(shape)), 'static4 = %.4f' % static4(shape), 't = %.4f' % t)
