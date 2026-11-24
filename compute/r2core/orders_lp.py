"""R2-core part 2: the Fano-template game for EVERY order of the six requests.

Why only the Fano shape: for n < 11k/6 every bad 7-tuple contains a full Fano plane of
miss-patterns (ROADMAP 2.2, floating MILP), and a set of lines meeting every Fano line contains a
line, so every miss-pattern contains a line: the closure shape is the Fano shape, and what is
left to vary is which Fano line each edge plays and the order of the requests.  One anchor E and
six requests in any order covers the 2- and 3-anchor versions (their anchors are edges the
requester can only obtain as responses in this instance).

Exact rational LP as in template_lp.py, for an arbitrary order.  Adversary policy:
  step 1: all drops on E-points or all on non-E points (two scenarios, chosen after the request);
  step r >= 2: all drops on points of one designated history type (E or non-E, and the exact
          set of earlier requests containing them), taken from the bulk classes of the template.
The policy is searched (first the "useless by cost" choice, then alternatives); an infeasible LP
proves that the adversary wins this order (model and availability assumption as in part 1).

usage: py orders_lp.py [c/g=3.01]
"""
import os, sys, itertools, random
from fractions import Fraction as Fr
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r1"))
from exact_infeasible import feasible

LINES = [frozenset(s) for s in ({1, 2}, {3, 4}, {1, 3}, {2, 4}, {1, 4}, {2, 3})]      # a-points on 1A..3B
ASTARS = {p: frozenset(i for i in range(6) if p in LINES[i]) for p in (1, 2, 3, 4)}
BPAIRS = {j: frozenset({2 * j, 2 * j + 1}) for j in range(3)}
SUBSETS = [frozenset(c) for n in range(7) for c in itertools.combinations(range(6), n)]


def okE(a): return any(s <= a for s in ASTARS.values())
def okN(a): return okE(a) or any(p <= a for p in BPAIRS.values())
def minimal(sets): return [r for r in sets if not any(q < r for q in sets)]


def bulk_types(order, r):
    """history types of the 7 template classes just before step r that are on offer at step r:
    (isE, set of earlier lines requesting the class, cost-before, cost-after-a-drop)."""
    L = order[r]; past = set(order[:r]); fut = set(order[r + 1:])
    out = []
    for isE, star in [(True, s) for s in ASTARS.values()] + [(False, s) for s in BPAIRS.values()]:
        if L in star: continue
        P = frozenset(star & past)
        ok = okE if isE else okN
        def cost(absent):
            best = 9
            for F in SUBSETS:
                if F <= fut and ok(absent | F): best = min(best, len(F))
            return best
        out.append((isE, P, cost(P), cost(P | {L})))
    return out


def build(c, g, order, policy):
    """policy[r] for r = 1..5: (isE, P).  Returns (A, b) for the two-scenario LP."""
    T = Fr(3, 4) + g; s = c - g; L1 = order[0]
    cols = []
    for sc in ("E", "N"):
        cols += [(sc, "e", R) for R in minimal([R for R in SUBSETS if okE(R)])]
        cols += [(sc, "f", R) for R in minimal([R for R in SUBSETS if okN(R)])]
        if sc == "E": cols += [(sc, "d0", R) for R in minimal([R for R in SUBSETS if L1 not in R and okE(R | {L1})])]
        else: cols += [(sc, "d0", R) for R in minimal([R for R in SUBSETS if L1 not in R and okN(R | {L1})])]
        for r in range(1, 6):
            isE, P = policy[r]; L = order[r]; past = set(order[:r]); ok = okE if isE else okN
            cand = [R for R in SUBSETS if R & past == P and L not in R and ok(R | {L})]
            cols += [(sc, "d%d" % r, R) for R in minimal(cand)]
        cols += [(sc, "y", L) for L in range(6)]
    n = len(cols); A = []; b = []
    def isEcol(col):
        sc, cat, R = col
        if cat == "e": return True
        if cat == "f" or cat == "y": return False
        if cat == "d0": return sc == "E"
        return policy[int(cat[1:])][0]
    def eq(row, rhs):
        A.append(row); b.append(rhs); A.append([-v for v in row]); b.append(-rhs)
    def row(pred):
        return [Fr(pred(col)) for col in cols]
    for sc in ("E", "N"):
        eq(row(lambda col: int(col[0] == sc and col[1] != "y" and isEcol(col))), Fr(1))
        eq(row(lambda col: int(col[0] == sc and col[1] != "y" and not isEcol(col))), Fr(3, 4) + c)
        for L in range(6):
            eq(row(lambda col: int(col[0] == sc and ((col[1] != "y" and L in col[2]) or (col[1] == "y" and col[2] == L)))), T)
        for r in range(6):
            Lr = order[r]
            eq(row(lambda col: (1 if col[1] == "d%d" % r else (-1 if (col[1] == "y" and col[2] == Lr) else 0)) if col[0] == sc else 0), s)
    def diff(pred):
        return [Fr(int(col[0] == "E" and pred(col)) - int(col[0] == "N" and pred(col))) for col in cols]
    eq(diff(lambda col: col[1] != "y" and isEcol(col) and L1 in col[2]), Fr(0))
    eq(diff(lambda col: col[1] != "y" and not isEcol(col) and L1 in col[2]), Fr(0))
    eq(diff(lambda col: col[1] == "y" and col[2] == L1), Fr(0))
    return A, b


def adversary_policy(order, c, g, tries=40, seed=0):
    """search a policy whose LP is infeasible; returns (policy, number of LPs) or (None, n)."""
    options = [None] + [bulk_types(order, r) for r in range(1, 6)]
    def pick(r, k):
        ts = sorted(options[r], key=lambda t: (t[3] < t[2], t[2], not t[0]))      # useless first, then low cost
        return ts[k % len(ts)][:2]
    rng = random.Random(seed); nlp = 0
    cand = [[0] * 6] + [[0] + [rng.randrange(4) for _ in range(5)] for _ in range(tries)]
    for ks in cand:
        policy = [None] + [pick(r, ks[r]) for r in range(1, 6)]
        A, b = build(c, g, order, policy); nlp += 1
        if not feasible(A, b): return policy, nlp
    return None, nlp


if __name__ == "__main__":
    ratio = Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(301, 100)
    g = Fr(1, 100); c = ratio * g
    names = ["1A", "1B", "2A", "2B", "3A", "3B"]
    # by symmetry (the stabilizer of E is transitive on the other six lines) the first request is 1A
    orders = [(0,) + p for p in itertools.permutations(range(1, 6))]
    won = 0; fails = []
    for order in orders:
        pol, nlp = adversary_policy(order, c, g)
        if pol is None: fails.append(order)
        else: won += 1
        print(" ".join(names[i] for i in order), "adversary wins" if pol else "NOT CERTIFIED", f"({nlp} LPs)",
              "" if not pol else "drops: " + "; ".join(("E" if t[0] else "nonE") + "{" + ",".join(names[i] for i in sorted(t[1])) + "}" for t in pol[1:]), flush=True)
    print(f"c/g = {ratio}: adversary certified to win {won} of {len(orders)} orders; not certified: {len(fails)}")
