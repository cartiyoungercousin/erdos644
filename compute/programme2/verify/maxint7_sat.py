"""Second, independent method for 'N < 11/6 => every good seven is Fano-type' (CEGAR with SAT).

Variables x_G (G subset of [7]): G in M.  M maximal intersecting <=> exactly one of G, G^c and up-closed.
M not a Fano up-set: for each of the 30 planes, some set containing a line is NOT in M.
Certificate w (rational, w >= 0, sum w >= 11/6): every M containing U_w = {G : w(G) > 1}
has LP(M) >= sum w (w is dual feasible: for F in M, w([7]\\F) <= 1).  We forbid sigma(U_w) inside M for
all sigma in S_7 and iterate.  UNSAT  =>  every non-Fano maximal M has a certificate => claim.
Each certificate is re-checked in exact arithmetic; the dual is found by LP on the current M.
"""
import itertools, sys
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
from pysat.solvers import Solver

FULL = 127
var = lambda g: g + 1
PERMS = list(itertools.permutations(range(7)))
def img(g, p):
    return sum(1 << p[i] for i in range(7) if g >> i & 1)

def base_clauses():
    cl = []
    for g in range(128):
        cl.append([var(g), var(FULL ^ g)]); cl.append([-var(g), -var(FULL ^ g)])
        for i in range(7):
            if not g >> i & 1: cl.append([-var(g), var(g | 1 << i)])
    base = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
    planes = {frozenset(sum(1 << p[a] for a in l) for l in base) for p in PERMS}
    assert len(planes) == 30
    for lines in planes:
        up = [g for g in range(128) if any(g & l == l for l in lines)]
        cl.append([-var(g) for g in up])
    return cl

def certificate(M):
    Ms = sorted(M)
    A = np.array([[0 if F >> i & 1 else 1 for i in range(7)] for F in Ms], dtype=float)  # rows: members
    r = linprog(-np.ones(7), A_ub=A, b_ub=np.ones(len(Ms)), bounds=[(0, None)] * 7, method='highs')
    if r.status == 3:   # unbounded dual = infeasible primal (impossible for a non-dictator)
        return None
    w = [Fr(x).limit_denominator(5040) for x in r.x]
    mx = max(sum(w[i] for i in range(7) if not F >> i & 1) for F in Ms)
    if mx > 1: w = [x / mx for x in w]
    assert all(x >= 0 for x in w)
    assert all(sum(w[i] for i in range(7) if not F >> i & 1) <= 1 for F in Ms)  # exact dual feasibility
    return w

THR = Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(11, 6)  # control: run with 15/8 -> must find 11/6

def main():
    s = Solver(name='cadical153', bootstrap_with=base_clauses())
    certs, it = [], 0
    while s.solve():
        it += 1
        model = s.get_model()
        M = {g for g in range(128) if model[g] > 0}
        w = certificate(M)
        if w is None:
            # dictator family: no pattern at all lives on it; forbid its orbit directly
            a = next(i for i in range(7) if (1 << i) in M)
            for i in range(7): s.add_clause([-var(1 << i)])
            continue
        W = sum(w)
        if W < THR:
            print('COUNTEREXAMPLE CANDIDATE: non-Fano M with LP', W); print(sorted(M)); sys.exit(1)
        U = [g for g in range(128) if sum(w[i] for i in range(7) if g >> i & 1) > 1]
        Umin = [g for g in U if not any((g & ~(1 << i)) in U for i in range(7) if g >> i & 1)]
        certs.append((W, w))
        seen = set()
        for p in PERMS:
            c = frozenset(img(g, p) for g in Umin)
            if c in seen: continue
            seen.add(c); s.add_clause([-var(g) for g in c])
    print('UNSAT after', it, 'iterations;', len(certs), 'certificates; min certificate value',
          min(c[0] for c in certs) if certs else None)
    for W, w in sorted(certs)[:5]:
        print(' ', W, [str(x) for x in w])

if __name__ == '__main__':
    main()
