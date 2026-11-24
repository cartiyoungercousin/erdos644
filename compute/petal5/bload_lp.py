"""PETAL §27.2: worst-case B-load of the centre phase of strategy PS2 (exact LP over the vertices of the adversary's
leak polytope).  delta = 1.

Adversary: masses of B (petal points outside R_X) by petal type J (singles {a}; multi-types J, 2 <= |J| <= 3, pool only);
petal a spends at most delta: sum_{J contains a} m_J <= 1.
Her design: each B point of type J is put into a pattern P (the set of centre requests containing it), P a nonempty
subset of {1,2,3}.  Safety (P2): |P| >= 2 (point in at most one centre), except singles of the S-petals:
  S_1-petal a (T_a cap R_X sits in G_1): its singles may have P = {1}; then all B points of type [4]-{a} need 1 in P;
  S_2-petal 4 (T_4 cap R_X = W_4 sits in G_2): its singles may have P = {2}; then all B points of type {1,2,3} need 2 in P.
Value = min over her choices (S_1 in {none,1,2,3}, S_2 in {none,4}) of the least max load.  g(m) is convex, so the max is
at a vertex; vertices have support <= 4 and are enumerated by solving the tight budget rows.
"""
import itertools, sys
from fractions import Fraction as Fr
import numpy as np
import highspy

TYPES = [frozenset([a]) for a in range(4)] + [frozenset(J) for r in (2, 3) for J in itertools.combinations(range(4), r)]
PATS = [frozenset(P) for r in (1, 2, 3) for P in itertools.combinations(range(3), r)]


def allowed(J, s1, s2):
    out = []
    for P in PATS:
        ok = len(P) >= 2
        if len(J) == 1:
            a = next(iter(J))
            if a == s1 and 0 in P: ok = True
            if a == s2 and 1 in P: ok = True
        if s1 is not None and J == frozenset(range(4)) - {s1} and 0 not in P: ok = False
        if s2 is not None and J == frozenset(range(4)) - {s2} and 1 not in P: ok = False
        if ok: out.append(P)
    return out


def best_design(m, s1, s2):
    h = highspy.Highs(); h.setOptionValue("output_flag", False)
    var = []
    h.addVar(0, highspy.kHighsInf)  # L
    idx = 1
    rows_load = [[] for _ in range(3)]
    for J, mass in zip(TYPES, m):
        if mass <= 1e-12: continue
        pats = allowed(J, s1, s2)
        if not pats: return float("inf")
        ids = []
        for P in pats:
            h.addVar(0, highspy.kHighsInf); ids.append(idx)
            for j in P: rows_load[j].append(idx)
            idx += 1
        h.addRow(mass, mass, len(ids), np.array(ids, dtype=np.int32), np.ones(len(ids)))
    for j in range(3):
        ids = rows_load[j] + [0]
        coef = [1.0] * len(rows_load[j]) + [-1.0]
        h.addRow(-highspy.kHighsInf, 0, len(ids), np.array(ids, dtype=np.int32), np.array(coef))
    h.changeColCost(0, 1.0)
    h.run()
    return h.getInfo().objective_function_value


def value(m, use_S=True):
    opts = [(None, None)]
    if use_S:
        opts = [(s1, s2) for s1 in (None, 0, 1, 2) for s2 in (None, 3)]
    return min(best_design(m, s1, s2) for s1, s2 in opts)


def vertices():
    n = len(TYPES)
    A = np.array([[1.0 if a in J else 0.0 for J in TYPES] for a in range(4)])
    seen = set()
    for r in range(1, 5):
        for supp in itertools.combinations(range(n), r):
            for tight in itertools.combinations(range(4), r):
                M = A[np.ix_(tight, supp)]
                if abs(np.linalg.det(M)) < 1e-9: continue
                x = np.linalg.solve(M, np.ones(r))
                if (x < -1e-9).any(): continue
                m = np.zeros(n); m[list(supp)] = x
                if (A @ m > 1 + 1e-9).any(): continue
                key = tuple(np.round(m, 9))
                if key in seen: continue
                seen.add(key)
                yield m


if __name__ == "__main__":
    worst, worstD, arg = -1, -1, None
    cnt = 0
    for m in vertices():
        cnt += 1
        v = value(m); vD = value(m, use_S=False)
        if v > worst + 1e-9: worst, arg = v, m
        worstD = max(worstD, vD)
    print("vertices:", cnt)
    print("worst B-load with S-petals (units of delta): %.6f at %s" % (worst, {"".join(str(a + 1) for a in sorted(J)): round(x, 4) for J, x in zip(TYPES, arg) if x > 1e-9}))
    print("worst B-load, double seal only: %.6f  (= 8/3 expected)" % worstD)
