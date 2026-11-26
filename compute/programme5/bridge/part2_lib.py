"""Bridge-seed families (part 2): shared exact tools. [computed exact] for tau / seven verdicts.
spectrum(k): allowed pairwise intersection sizes s (distinct members) avoiding the open gaps
(0.268, 5/14) and (0.435, 10/21) in units of k (exact rationals).
tau(fam, n): exact min transversal by HiGHS ILP (scipy.optimize.milp).
seven(fam, n, forced): exact SAT (CaDiCaL + seqcounter <= 7): some <= 7 members (containing all 'forced')
with no 2-point transversal, i.e. every pair {x,y} (x=y allowed) is avoided by a chosen member.
check_seven: brute-force verification of a claimed seven (no pair of points meets all chosen members)."""
import itertools, random
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from pysat.solvers import Cadical153, Cadical195
from pysat.card import CardEnc, EncType

G1 = (Fr(268, 1000), Fr(5, 14)); G2 = (Fr(435, 1000), Fr(10, 21))

def spectrum(k):
    ok = []
    for s in range(k):
        f = Fr(s, k)
        if G1[0] < f < G1[1] or G2[0] < f < G2[1]: continue
        ok.append(s)
    return ok

def record(k): return (3 * k + 5) // 4

def tau(fam, n, rng=None):
    m = len(fam)
    A = np.zeros((m, n))
    for i, B in enumerate(fam):
        for v in B: A[i, v] = 1
    c = np.ones(n)
    if rng is not None: c = c + np.array([rng.random() for _ in range(n)]) / (10.0 * n)
    r = milp(c, constraints=LinearConstraint(A, lb=1, ub=np.inf), integrality=np.ones(n), bounds=Bounds(0, 1))
    assert r.status == 0
    S = [v for v in range(n) if r.x[v] > 0.5]
    return len(S), S

def seven(fam, n, forced=()):
    m = len(fam)
    cnf = CardEnc.atmost(lits=list(range(1, m + 1)), bound=7, top_id=m, encoding=EncType.seqcounter)
    s = Cadical153(bootstrap_with=cnf.clauses)
    for f in forced: s.add_clause([f + 1])
    # pairs avoided by a forced member are already covered (exact reduction)
    for x in range(n):
        for y in range(x, n):
            if any(x not in fam[f] and y not in fam[f] for f in forced): continue
            s.add_clause([i + 1 for i, B in enumerate(fam) if x not in B and y not in B])
    if not s.solve(): s.delete(); return None
    ch = [v - 1 for v in s.get_model() if 0 < v <= m]; s.delete()
    assert check_seven([fam[i] for i in ch], n)
    return ch

def check_seven(mem, n):
    if not (1 <= len(mem) <= 7): return False
    for x in range(n):
        for y in range(x, n):
            if all(x in B or y in B for B in mem): return False
    return True

def uncovered_points(others, n):
    """W = points x lying in some pair {x,y} (x=y allowed) that meets every member of 'others'."""
    W = set()
    for x in range(n):
        for y in range(x, n):
            if all(x in B or y in B for B in others): W.add(x); W.add(y)
    return W

def cotype_summary(mem, cells, n):
    """cells: list of (name, set). Returns {cell: {cotype-string: count}} (cotype = indices of members missing x)."""
    out = {}
    for name, C in cells:
        d = {}
        for x in sorted(C):
            I = "".join(str(i) for i, B in enumerate(mem) if x not in B) or "-"
            d[I] = d.get(I, 0) + 1
        out[name] = d
    return out

def seven_budget(fam, n, forced, budget):
    """As seven(), but with a conflict budget: returns list (seven found, verified), None (UNSAT: no seven
    containing the forced members, exact) or 'unknown' (budget exhausted)."""
    m = len(fam)
    cnf = CardEnc.atmost(lits=list(range(1, m + 1)), bound=7, top_id=m, encoding=EncType.seqcounter)
    s = Cadical195(bootstrap_with=cnf.clauses)
    for f in forced: s.add_clause([f + 1])
    for x in range(n):
        for y in range(x, n):
            if any(x not in fam[f] and y not in fam[f] for f in forced): continue
            s.add_clause([i + 1 for i, B in enumerate(fam) if x not in B and y not in B])
    s.conf_budget(budget); r = s.solve_limited()
    if r is None: s.delete(); return "unknown"
    if not r: s.delete(); return None
    ch = [v - 1 for v in s.get_model() if 0 < v <= m]; s.delete()
    assert check_seven([fam[i] for i in ch], n)
    return ch
