"""PETAL Part III: best triple-free 2+2 quadruple inside the exact-leak two-arena family H_delta.
Arenas V_A, V_F of mass n = 1 + t/2 - delta.  Colour-A edges: mass 1-delta in V_A (alpha) and delta in V_F (beta);
colour-F edges: 1-delta in V_F (phi), delta in V_A (gamma).  Quad = (A1, A2, F1, F2), no point in three of them.
Minimise over quad shapes AND 3-round designs (Theorem K(i), with the empty type allowed opposite an exactly empty cell)
the maximum round load.  One MILP.   usage: py quadmin.py t delta [n]
"""
import sys, itertools
from lpw import Model, esum

def add_design(M, cells6, L):
    """cells6: dict (i,j)->expr for petals 0..3.  Adds Theorem K design with max load <= L."""
    grids = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
    TYPES = range(8)
    load = [[], [], []]
    for (ca, cb) in grids:
        x = {F: M.var() for F in TYPES}; y = {F: M.var() for F in TYPES}
        u = {F: M.var(0, 1, True) for F in TYPES}; v = {F: M.var(0, 1, True) for F in TYPES}
        for F in TYPES:
            M.le(x[F], 2 * u[F]); M.le(y[F], 2 * v[F])
            for G in TYPES:
                if F & G == 0: M.le(u[F] + v[G], 1)
        M.eq(esum(x.values()), cells6[ca]); M.eq(esum(y.values()), cells6[cb])
        for i in range(3):
            load[i] += [x[F] for F in TYPES if F >> i & 1] + [y[F] for F in TYPES if F >> i & 1]
    for i in range(3): M.le(esum(load[i]), L)

def quadmin(t, delta, n=None, msg=False):
    if n is None: n = 1 + t / 2 - delta
    own = 1 - delta
    M = Model(msg)
    L = M.var()
    subs = [s for r in range(3) for s in itertools.combinations(range(4), r)]
    at = {X: {s: M.var() for s in subs} for X in "AF"}
    for X in "AF":
        M.eq(esum(at[X].values()), n)
        for lab in range(4):
            M.eq(esum(v for s, v in at[X].items() if lab in s), own if lab < 2 else 1 - own)
    # petals 0=A1,1=A2,2=F1,3=F2.  V_A labels (a1,a2,g1,g2) = petals (0,1,2,3); V_F labels (phi1,phi2,b1,b2) = petals (2,3,0,1)
    mapF = {0: 2, 1: 3, 2: 0, 3: 1}
    cell = {}
    for i, j in itertools.combinations(range(4), 2):
        cell[(i, j)] = at["A"][(i, j)] + at["F"][tuple(sorted((mapF[i], mapF[j])))]
    add_design(M, cell, L)
    st, val = M.minimize(L)
    return st, val, {k: round(M.val(v), 4) for k, v in cell.items()}

if __name__ == "__main__":
    t = float(sys.argv[1]); d = float(sys.argv[2])
    n = float(sys.argv[3]) if len(sys.argv) > 3 else None
    print(quadmin(t, d, n))
