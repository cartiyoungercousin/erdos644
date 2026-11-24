"""Independent continuous design value L(a,b) for PETAL Theorem K, via maximal cross-intersecting pairs
of families of nonempty subsets of [3] (one LP per choice of pair per grid), compared with
  (a) TWIN 15.4 closed form L*(a,b) for one grid, (b) compute/petal/design.py MILP (the author's)."""
import itertools, random, sys
import highspy
inf = highspy.kHighsInf
TYPES = list(range(1, 8))

def maximal_pairs():
    def N(F):
        return frozenset(G for G in TYPES if all(G & f for f in F))
    pairs = set()
    for mask in range(1 << 7):
        F = frozenset(t for i, t in enumerate(TYPES) if mask >> i & 1)
        G = N(F); F2 = N(G)
        pairs.add((F2, G))
    return sorted(pairs, key=lambda p: (len(p[0]), sorted(p[0])))

PAIRS = maximal_pairs()

def lp(cells, choice):
    h = highspy.Highs(); h.setOptionValue("output_flag", False)
    n = 0
    L = 0; h.addVar(0, inf); h.changeColCost(L, 1.0); n = 1
    load = [[], [], []]
    for (a, b), (F, G) in zip(cells, choice):
        for side, fam, m in ((0, F, a), (1, G, b)):
            if m == 0: continue
            idx = []
            for T in fam:
                h.addVar(0, inf); idx.append(n)
                for i in range(3):
                    if T >> i & 1: load[i].append(n)
                n += 1
            if not idx: return None
            h.addRow(m, m, len(idx), idx, [1.0] * len(idx))
    for i in range(3):
        idx = load[i] + [L]; val = [1.0] * len(load[i]) + [-1.0]
        h.addRow(-inf, 0, len(idx), idx, val)
    h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal: return None
    return h.getInfo().objective_function_value

def design(cells):
    """cells: list of 3 (a_r,b_r).  zero => no edge on that grid (true emptiness)."""
    best = 1e9
    for choice in itertools.product(PAIRS, repeat=3):
        # skip choices for empty grids beyond one
        v = lp(cells, choice)
        if v is not None and v < best: best = v
    return best

def lstar(a, b):
    c = [a + b / 3, b + a / 3, 2 * (a + b) / 3]
    if b >= a / 2: c.append(3 * a / 4 + b / 2)
    if a >= b / 2: c.append(3 * b / 4 + a / 2)
    return min(c)

if __name__ == "__main__":
    print("maximal pairs:", len(PAIRS))
