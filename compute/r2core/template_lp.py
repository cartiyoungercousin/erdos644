"""R2-core: the adaptive Fano-template game on n = 7k/4 + c points, budget T = 3k/4 + g.

Exact rational LP (two-scenario deterministic equivalent) for the requester's best play against
an explicit adversary policy PI.  If the LP is infeasible, the adversary wins against every
requester play covered by the model (see notes/R2CORE_RESULTS.md, Section 1, for what "covered"
means); if it is feasible, PI fails and the solution is a requester line of play against PI.

Normalization k = 1.  s = c - g.  Lines 0..5 = 1A,1B,2A,2B,3A,3B (asked in this order):
  1A={a1,a2} 1B={a3,a4} 2A={a1,a3} 2B={a2,a4} 3A={a1,a4} 3B={a2,a3}.
A point is "covered" iff the set of lines it is absent from (requested or dropped) contains
  E-point:      an a-star {0,2,4}, {0,3,5}, {1,2,5} or {1,3,4};
  non-E point:  a group pair {0,1}, {2,3}, {4,5} (star b_j, E itself being the third line)
                or an a-star.
Requester: for every type of point, the set R of lines whose requests contain it; request L has
size T - y_L.  Response L drops exactly s + y_L offered points.

Adversary policy PI:
  at 1A: either all drops on E-points (scenario "E") or all on non-E points (scenario "N"),
         chosen after seeing the first request;
  at 1B: drops E-points that were requested at 1A (two absences in the same group);
  at 2A,2B,3A,3B: drops non-E points that are already absent from 1A and 1B (complete).
The drops at 2A..3B never change coverage.  The model assumes they are available: at each of
these responses at least s + y_L complete points are on offer (true unless the requester spends
a bulk part of a request on already complete points).

Non-anticipativity: at the time of the first request all E-points are alike and all non-E points
are alike, so the first move is (E-amount at 1A, non-E amount at 1A, y_1A), shared by the two
scenarios; everything later may depend on the scenario.

usage: py template_lp.py            (prints the table used in the notes)
"""
import os, sys, itertools
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r1"))
from exact_infeasible import feasible          # exact two-phase simplex over Fractions

ASTARS = [frozenset(s) for s in ({0, 2, 4}, {0, 3, 5}, {1, 2, 5}, {1, 3, 4})]
BPAIRS = [frozenset(s) for s in ({0, 1}, {2, 3}, {4, 5})]
SUBSETS = [frozenset(c) for n in range(7) for c in itertools.combinations(range(6), n)]


def okE(absent): return any(s <= absent for s in ASTARS)
def okN(absent): return any(s <= absent for s in ASTARS) or any(p <= absent for p in BPAIRS)


def minimal(sets):
    """keep only inclusion-minimal request sets (a superset costs more and covers nothing new)."""
    return [r for r in sets if not any(q < r for q in sets)]


def build(c, g, scenarios=("E", "N")):
    T = Fr(3, 4) + g; s = c - g
    cols = []                       # (scenario, category, R)
    for sc in scenarios:
        cols += [(sc, "e", R) for R in minimal([R for R in SUBSETS if okE(R)])]
        cols += [(sc, "eD2", R) for R in minimal([R for R in SUBSETS if 0 in R and 1 not in R and okE(R | {1})])]
        cols += [(sc, "f", R) for R in minimal([R for R in SUBSETS if okN(R)])]
        if sc == "E":
            cols += [(sc, "eD1", R) for R in minimal([R for R in SUBSETS if 0 not in R and okE(R | {0})])]
        else:
            cols += [(sc, "h", R) for R in minimal([R for R in SUBSETS if 0 not in R and okN(R | {0})])]
        cols += [(sc, "y", L) for L in range(6)]
    idx = {col: i for i, col in enumerate(cols)}
    n = len(cols); A = []; b = []
    def eq(row, rhs):
        A.append(row); b.append(rhs); A.append([-v for v in row]); b.append(-rhs)
    def row_of(pred):
        r = [Fr(0)] * n
        for col, i in idx.items():
            v = pred(col)
            if v: r[i] = Fr(v)
        return r
    isE = ("e", "eD1", "eD2"); isN = ("f", "h")
    for sc in scenarios:
        eq(row_of(lambda col: col[0] == sc and col[1] in isE), Fr(1))
        eq(row_of(lambda col: col[0] == sc and col[1] in isN), Fr(3, 4) + c)
        for L in range(6):
            eq(row_of(lambda col: col[0] == sc and ((col[1] != "y" and L in col[2]) or (col[1] == "y" and col[2] == L))), T)
        # drops at 1B: E-points requested at 1A, amount s + y_1B
        eq(row_of(lambda col: col[0] == sc and (1 if col[1] == "eD2" else (-1 if (col[1] == "y" and col[2] == 1) else 0))), s)
        # drops at 1A: amount s + y_1A, on E (scenario E) or non-E (scenario N)
        cat = "eD1" if sc == "E" else "h"
        eq(row_of(lambda col: col[0] == sc and (1 if col[1] == cat else (-1 if (col[1] == "y" and col[2] == 0) else 0))), s)
    if len(scenarios) == 2:
        a, bb = scenarios
        def diff(pred):
            return [x - y for x, y in zip(row_of(lambda col: col[0] == a and pred(col)), row_of(lambda col: col[0] == bb and pred(col)))]
        eq(diff(lambda col: col[1] in isE and 0 in col[2]), Fr(0))           # E-amount requested at 1A
        eq(diff(lambda col: col[1] in isN and 0 in col[2]), Fr(0))           # non-E amount requested at 1A
        eq(diff(lambda col: col[1] == "y" and col[2] == 0), Fr(0))           # unused budget at 1A
    return A, b, cols


def requester_can_win(c, g, scenarios=("E", "N")):
    A, b, cols = build(Fr(c), Fr(g), scenarios)
    return feasible(A, b), len(cols), len(A)


if __name__ == "__main__":
    print("exact rational LP; True = the requester has a play that beats the adversary policy")
    print("%-28s %-10s %-10s %-12s" % ("(c, g) with k = 1", "both", "E only", "N only"))
    cases = [("c/g = 2", Fr(2, 100), Fr(1, 100)), ("c/g = 3", Fr(3, 100), Fr(1, 100)), ("c/g = 3.01", Fr(301, 10000), Fr(1, 100)),
             ("c/g = 4", Fr(4, 100), Fr(1, 100)), ("c/g = 6", Fr(6, 100), Fr(1, 100)), ("c/g = 10", Fr(10, 100), Fr(1, 100)),
             ("c/g = 4, g = 1/1000", Fr(4, 1000), Fr(1, 1000)), ("c/g = 10, g = 1/1000", Fr(10, 1000), Fr(1, 1000)),
             ("K_N, N<7k/4: c=-1%, g=-2%", Fr(-1, 100), Fr(-2, 100)), ("K_N: c=-2%, g=-5%", Fr(-2, 100), Fr(-5, 100))]
    for name, c, g in cases:
        both, nv, nr = requester_can_win(c, g)
        e_only = requester_can_win(c, g, ("E",))[0]
        n_only = requester_can_win(c, g, ("N",))[0]
        print("%-28s %-10s %-10s %-12s" % (name, both, e_only, n_only), flush=True)
    print(f"(LP size: {nv} variables, {nr} inequality rows)")
