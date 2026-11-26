"""Type engine for adaptive closures of a pencil (E,F,G) (units: member size KK, request size t).

A position is a list of atoms (type, mass, present); type = bitmask of the members containing the atom's points
(bit 0 = E, 1 = F, 2 = G, 3.. = later answers).  'present' = the atom has at least one point (mass may be 0: a 0+ atom).
A request U gives every atom a requested mass u_a (0+ atoms: u_a = FULL means requested entirely, at zero cost).
An answer M avoids U: in-mass v_a <= mass_a - u_a, total <= KK (answers inside V; maximal answers dominate).
The adversary makes every part he may make nonempty nonempty (more candidate pairs only help him).
finish(pos, S, r): least max load of r static blocks covering every candidate pair of the kept members S
(a pair {p,q} with type_p | type_q containing S); exact MILP over all patterns (subsets of the r blocks).
A point whose type contains S makes the finish impossible (it pairs with every point of the ground set).
"""
import itertools, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix

EPS = 1e-9
FULL = -1.0

def patterns(r):
    return list(range(1, 1 << r))

_DISJ = {}
def disj(r):
    if r not in _DISJ:
        P = patterns(r)
        _DISJ[r] = [(i, j) for i, p in enumerate(P) for j, q in enumerate(P) if p & q == 0 and i < j] + \
                   [(i, j) for i, p in enumerate(P) for j, q in enumerate(P) if p & q == 0 and i > j]
    return _DISJ[r]

def finish(atoms, S, r, need_cover=None):
    """atoms: list of (type, mass, present). Returns least max block load (inf if impossible)."""
    pres = [(ty, m) for (ty, m, p) in atoms if p]
    if any((ty & S) == S for ty, m in pres): return np.inf
    # merge atoms by restricted type (points with the same trace on S are interchangeable)
    agg = {}
    for ty, m in pres:
        k = ty & S
        agg[k] = agg.get(k, 0.0) + m
    types = sorted(agg)
    edges = [(i, j) for i in range(len(types)) for j in range(i + 1, len(types)) if (types[i] | types[j]) == S]
    inv = sorted(set([i for e in edges for i in e]))
    if not edges: return 0.0
    if r == 0: return np.inf
    idx = {a: n for n, a in enumerate(inv)}
    P = patterns(r); nP = len(P)
    nb = len(inv) * nP; nv = 2 * nb + 1
    bi = lambda a, s: idx[a] * nP + s
    wi = lambda a, s: nb + idx[a] * nP + s
    D = disj(r)
    rows = []; lo = []; hi = []
    A = lil_matrix((len(inv) * (2 + nP) + len(edges) * len(D) + r, nv))
    row = 0
    for a in inv:
        m = agg[types[a]]
        for s in range(nP): A[row, wi(a, s)] = 1
        lo.append(m); hi.append(m); row += 1
        for s in range(nP): A[row, bi(a, s)] = 1
        lo.append(1); hi.append(np.inf); row += 1
        for s in range(nP):
            A[row, wi(a, s)] = 1; A[row, bi(a, s)] = -m; lo.append(-np.inf); hi.append(0); row += 1
    for (a, c) in edges:
        for (s1, s2) in D:
            if s1 < s2:
                A[row, bi(a, s1)] += 1; A[row, bi(c, s2)] += 1; lo.append(-np.inf); hi.append(1); row += 1
                A[row, bi(a, s2)] += 1; A[row, bi(c, s1)] += 1; lo.append(-np.inf); hi.append(1); row += 1
    for g in range(r):
        for a in inv:
            for s in range(nP):
                if P[s] >> g & 1: A[row, wi(a, s)] = 1
        A[row, nv - 1] = -1; lo.append(-np.inf); hi.append(0); row += 1
    A = A[:row].tocsr()
    c = np.zeros(nv); c[-1] = 1
    integ = np.zeros(nv); integ[:nb] = 1
    ub = np.full(nv, np.inf); ub[:nb] = 1
    res = milp(c, constraints=LinearConstraint(A, lo, hi), integrality=integ, bounds=Bounds(np.zeros(nv), ub),
               options={'disp': False, 'mip_rel_gap': 1e-9})
    return res.fun if res.status == 0 else np.inf

def best_finish(atoms, nmem, base=0b111, allow_drop_base=True, budget=7):
    """min over kept sets S (|S| >= 3, all non-base members optional) of finish with 7-|S| blocks."""
    best = (np.inf, None)
    allm = list(range(nmem))
    for size in range(min(nmem, budget), 2, -1):
        for S_ in itertools.combinations(allm, size):
            S = sum(1 << i for i in S_)
            if not allow_drop_base and (S & base) != base: continue
            v = finish(atoms, S, budget - size)
            if v < best[0]: best = (v, S)
    return best

def answer(atoms, u, v, newbit):
    """split atoms by the answer: u requested, v in-mass. Returns new atom list."""
    out = []
    for (ty, m, p), ua, va in zip(atoms, u, v):
        if not p: continue
        full = (ua == FULL) or (m - ua <= EPS and m > EPS)
        if not full:
            out.append((ty | newbit, va, True))
        out.append((ty, m - va, True))
    return out

def triple(x, y, z, KK=1.0):
    """pencil E(bit0),F(bit1),G(bit2): X=E&F, Y=E&G, Z=F&G (0 means 0+)."""
    X, Y, Z = x, y, z
    return [(3, X, True), (5, Y, True), (6, Z, True), (1, KK - X - Y, True), (2, KK - X - Z, True), (4, KK - Y - Z, True)]
