"""FRONTIER §2.1: integer rounding of TWIN Theorem C (the finite-k GAP of the 16.A verifier).

Claim [proved by hand in FRONTIER 2.1]: with the split below every round load is
  <= sum_ab ceil(p_ab/2) + sum_c ceil(q_c/2) <= |U|/2 + 3,
so Theorem C wins whenever |U| <= 2T - 6, and 16.A holds for n <= 3T - k/2 - 6.
Check: random integer anchor shapes; build explicit types; verify (i) the load bound,
(ii) Theorem B's criterion (every x in P_ab, y in B_c have intersecting kill types).
"""
import random, itertools

ROUNDS = (4, 5, 6, 7)
PTYPES = {(1, 2): [(4, 7), (5, 6)], (1, 3): [(4, 6), (5, 7)], (2, 3): [(4, 5), (6, 7)]}

def q_pairs(ab):
    bad = set(PTYPES[ab])
    pairs = [p for p in itertools.combinations(ROUNDS, 2) if p not in bad]
    # order as a 4-cycle so that the extra points go to non-adjacent edges first
    cyc = [pairs[0]]
    while len(cyc) < 4:
        last = cyc[-1]
        nxt = [p for p in pairs if p not in cyc and set(p) & set(last)
               and (len(cyc) < 3 or True)]
        # prefer an edge sharing a vertex with last and not with cyc[0] unless closing
        nxt.sort(key=lambda p: len(set(p) & set(cyc[0])))
        cyc.append(nxt[0])
    return cyc

def split(n, parts, order):
    base, extra = divmod(n, parts)
    sizes = [base] * parts
    for i in order[:extra]:
        sizes[i] += 1
    return sizes

def check(p12, p13, p23, k):
    p = {(1, 2): p12, (1, 3): p13, (2, 3): p23}
    q = {3: k - p13 - p23, 2: k - p12 - p23, 1: k - p12 - p13}
    if min(q.values()) < 0:
        return None
    pts = []  # (kind, label, type)
    for ab, (ta, tb) in PTYPES.items():
        a, b = split(p[ab], 2, [0, 1])
        pts += [("P", ab, ta)] * a + [("P", ab, tb)] * b
    opp = {3: (1, 2), 2: (1, 3), 1: (2, 3)}
    for c, ab in opp.items():
        cyc = q_pairs(ab)
        sizes = split(q[c], 4, [0, 2, 1, 3])
        for s, ty in zip(sizes, cyc):
            pts += [("Q", c, ty)] * s
    U = len(pts)
    load = max(sum(1 for x in pts if r in x[2]) for r in ROUNDS)
    bound = sum((v + 1) // 2 for v in p.values()) + sum((v + 1) // 2 for v in q.values())
    assert load <= bound <= U / 2 + 3, (p12, p13, p23, k, load, bound, U)
    # Theorem B criterion on types
    def in_anchor(x, c):
        kind, lab, _ = x
        return (c in lab) if kind == "P" else (lab == c)
    for x in pts:
        if x[0] != "P":
            continue
        a, b = x[1]
        c = ({1, 2, 3} - {a, b}).pop()
        for y in pts:
            if in_anchor(y, c):
                assert set(x[2]) & set(y[2]), (x, y)
    return load - U / 2

def main():
    random.seed(1)
    worst = -1e9
    for _ in range(3000):
        k = random.randint(4, 40)
        p12 = random.randint(0, k); p13 = random.randint(0, k - p12); p23 = random.randint(0, k)
        r = check(p12, p13, p23, k)
        if r is not None:
            worst = max(worst, r)
    print("all checks passed; worst load - |U|/2 =", worst, "(claim: <= 3)")

if __name__ == "__main__":
    main()
