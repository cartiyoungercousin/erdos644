"""Shared Fano/need-LP helpers for CORE §75-§79 (flag-algebra / type-space relaxation).
Members are labelled by Fano POINTS 0..6; a point x of V is good iff its co-type contains a LINE.
Class V_l (l a line) must lie in every kept member i in l; future member j must contain
L_j = union of classes of lines through j; it is requested as is iff |L_j| <= t."""
import itertools
import numpy as np
from scipy.optimize import linprog

LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]

def need(cells, kept_label, t, omega=None, future_cap=True):
    """cells: list of (mass, frozenset of kept-member indices containing the cell).
    kept_label: dict kept-member index -> Fano point.  Returns min sum_j u_j over future points j
    (|L_j| <= t + u_j, 0 <= u_j <= omega if omega given) or None if infeasible.
    """
    pts_kept = set(kept_label.values())
    fut = [p for p in range(7) if p not in pts_kept]
    inv = {p: i for i, p in kept_label.items()}
    var = []  # (cell idx, line idx)
    for ci, (m, ct) in enumerate(cells):
        for li, L in enumerate(LINES):
            if all((p not in inv) or (inv[p] in ct) for p in L):
                var.append((ci, li))
    nv = len(var); nu = len(fut)
    c = np.zeros(nv + nu); c[nv:] = 1
    Aeq = np.zeros((len(cells), nv + nu)); beq = np.array([m for m, _ in cells], float)
    for k, (ci, li) in enumerate(var):
        Aeq[ci, k] = 1
    Aub = np.zeros((nu, nv + nu)); bub = np.full(nu, t)
    for r, j in enumerate(fut):
        for k, (ci, li) in enumerate(var):
            if j in LINES[li]:
                Aub[r, k] = 1
        Aub[r, nv + r] = -1
    bounds = [(0, None)] * nv + [(0, omega)] * nu
    # cells with no admissible line -> infeasible
    for ci, (m, ct) in enumerate(cells):
        if m > 1e-12 and not any(v[0] == ci for v in var):
            return None
    res = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=beq, bounds=bounds, method='highs')
    return res.fun if res.status == 0 else None

def pair_cells(N, c, o):
    return [(o, frozenset({0,1})), (c-o, frozenset({0})), (c-o, frozenset({1})), (N-2*c+o, frozenset())]
