"""Falsification test of Corollary (slope 3/11) on ALL two-block families
H_J = {k-sets B : |B cap X| in J}, |X|=a <= |Y|=b, n=a+b <= 2k, J subset of [0,k].
tau computed exactly (n - largest hole).  Every family with tau > (3n+3k+C)/11 must have a good seven;
we look for a Fano-type seven by CP-SAT (own model).  usage: twoblock_check.py kmax C"""
import sys
from ortools.sat.python import cp_model
kmax, C = int(sys.argv[1]), int(sys.argv[2])
LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]

def tau(J, a, b, k):
    best = 0
    for x in range(a + 1):
        for y in range(b + 1):
            if x + y <= best: continue
            if not any(j <= x and k - j <= y for j in J): best = x + y
    return a + b - best

def fano_seven(J, a, b, k):
    m = cp_model.CpModel()
    xs = [m.NewIntVar(0, a, f'x{p}') for p in range(7)]
    ys = [m.NewIntVar(0, b, f'y{p}') for p in range(7)]
    m.Add(sum(xs) <= a); m.Add(sum(ys) <= b)   # leftover points get colour 0 (in no R)
    for L in LINES:
        X = sum(xs[p] for p in range(7) if p not in L); Y = sum(ys[p] for p in range(7) if p not in L)
        ch = []
        for j in J:
            if j > a or k - j > b: continue
            bv = m.NewBoolVar(''); m.Add(X >= j).OnlyEnforceIf(bv); m.Add(Y >= k - j).OnlyEnforceIf(bv); ch.append(bv)
        if not ch: return False
        m.AddBoolOr(ch)
    s = cp_model.CpSolver(); s.parameters.num_workers = 1; s.parameters.max_time_in_seconds = 60
    st = s.Solve(m)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE): return True
    if st == cp_model.INFEASIBLE: return False
    return None

viol = 0; tot = 0; unresolved = []
for k in range(2, kmax + 1):
    for n in range(k, 2 * k + 1):
        for a in range(0, n // 2 + 1):
            b = n - a
            for mask in range(1, 1 << (k + 1)):
                J = [j for j in range(k + 1) if mask >> j & 1]
                # canonical: only j feasible matter
                if any(j > a or k - j > b for j in J): continue
                tot += 1
                t = tau(J, a, b, k)
                if 11 * t > 3 * n + 3 * k + C:
                    viol += 1
                    f = fano_seven(J, a, b, k)
                    if f is not True: unresolved.append((k, n, a, J, t, f))
print(f"kmax={kmax} C={C}: families={tot} above-bound={viol} above-bound without Fano seven={len(unresolved)}")
for u in unresolved[:30]: print('  ', u)
