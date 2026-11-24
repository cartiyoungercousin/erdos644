"""CORE 46: the ordered frozen anti-plan family.

Cells O, U (= A + B), g, each with a fixed order.  Rule: if |S & O| < omega the dump is the first omega unrequested points
of O, otherwise the first omega unrequested points of U.  Members, as sets (first order):
  shape H:  K contains O1 (first omega of O) and |K & O| <= 2 omega;      shape L:  K contains U1 (first omega of U), |K & O| >= omega.
A line L_i lies in a member of shape H iff  |L_i & O2| <= omega  and  |L_i| - |L_i & O1| + omega <= c;
                              of shape L iff  |L_i| - |L_i & U1| + omega + max(0, omega - |L_i & O|) <= c.
Part 1 (float LP, HiGHS): for each of the 2^7 shape assignments, is there a Fano blow-up (classes x regions O1,O2,U1,U2,g)?
Part 2 (exact, Fractions): an explicit certificate for the all-H assignment (Theorem P with pool O1), verified exactly.
Part 3 (exact, finite k): the actual rule on real sets; the seven requests; brute-force pair-cover of the seven replies.
"""
import itertools, sys
from fractions import Fraction as Fr
from lpx import LP, INF

LINES = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]     # lines as triples of classes
REG = ["O1", "O2", "U1", "U2", "g"]


def masses(t, N, o):
    c = N - 1; om = c - t
    return {"O1": om, "O2": o - om, "U1": om, "U2": 2 * (c - o) - om, "g": N - 2 * c + o}


def feasible(t, N, o, shapes):
    c = N - 1; om = c - t; M = masses(t, N, o)
    if min(M.values()) < -1e-12: return None
    L = LP(); w = {(p, r): L.var() for p in range(7) for r in REG}
    for r in REG: L.row([(w[p, r], 1.0) for p in range(7)], M[r], M[r])
    for i, ln in enumerate(LINES):
        tot = [(w[p, r], 1.0) for p in ln for r in REG]
        if shapes[i] == "H":
            L.row([(w[p, "O2"], 1.0) for p in ln], -INF, om)
            L.row(tot + [(w[p, "O1"], -1.0) for p in ln], -INF, c - om)
        else:
            L.row(tot + [(w[p, "U1"], -1.0) for p in ln], -INF, c - om)
            L.row(tot + [(w[p, "U1"], -1.0) for p in ln] + [(w[p, r], -1.0) for p in ln for r in ("O1", "O2")], -INF, c - 2 * om)
    val, x = L.solve()
    return val is not None


def part1(t, N, o):
    res = {}
    for sh in itertools.product("HL", repeat=7): res["".join(sh)] = feasible(t, N, o, sh)
    ok = [s for s, v in res.items() if v]
    om = N - 1 - t
    print(f"t={t} N={N} o={o} omega={om:.3f} o/omega={o/om:.2f}: feasible shape assignments {len(ok)}/128; "
          f"all-H {res['HHHHHHH']}, all-L {res['LLLLLLL']}, pencil H + rest L {res['HHHLLLL']}, pencil L + rest H {res['LLLHHHH']}")
    return res


def part2(t, N, o):
    """explicit all-H certificate: kernel class 0 = O1 + (N - 3/2 - omega) of U2; O2 split evenly over the six other classes
    (needs (o - omega)/2 <= omega for the transversals and (o - omega)/3 <= omega for the pencil lines); rest even."""
    t, N, o = Fr(t), Fr(N), Fr(o); c = N - 1; om = c - t
    M = {"O1": om, "O2": o - om, "U1": om, "U2": 2 * (c - o) - om, "g": N - 2 * c + o}
    w = {(p, r): Fr(0) for p in range(7) for r in REG}
    w[0, "O1"] = om; w[0, "U2"] = N - Fr(3, 2) - om
    rest = dict(M); rest["O1"] = Fr(0); rest["U2"] -= w[0, "U2"]
    for p in range(1, 7):
        for r in REG: w[p, r] = rest[r] / 6
    assert all(v >= 0 for v in w.values()) and all(sum(w[p, r] for p in range(7)) == M[r] for r in REG)
    ok = True
    for ln in LINES:
        tot = sum(w[p, r] for p in ln for r in REG)
        ok &= sum(w[p, "O2"] for p in ln) <= om and tot - sum(w[p, "O1"] for p in ln) + om <= c
    print(f"  exact all-H certificate at t={t} N={N} o={o}: {'VALID' if ok else 'invalid'} "
          f"(pencil lines {sum(w[p, r] for p in LINES[0] for r in REG)} <= c={c}; transversals {sum(w[p, r] for p in LINES[3] for r in REG)} <= t={t})")
    return ok


def part3(k, T, n, o):
    """real sets.  V = O + U + g in this order; rule as stated; seven requests of the pool design; all pairs checked."""
    c = n - k; om = c - T; u = 2 * (c - o); gsz = n - 2 * c + o
    O = list(range(o)); U = list(range(o, o + u)); G = list(range(o + u, n))
    def reply(S):
        S = set(S); assert len(S) == T
        pool = O if len(S & set(O)) < om else U
        D = [x for x in pool if x not in S][:om]; assert len(D) == om
        return frozenset(S | set(D))
    # T-covering by construction; check the rule is always defined on a sample is implied by the asserts in use.
    wo = n - 3 * k // 2; assert 2 * wo == 2 * n - 3 * k and wo >= om
    O1 = O[:om]; O2 = O[om:]
    others = U + G                                             # non-O points, to be distributed
    kernel = O1 + others[:wo - om]; others = others[wo - om:]
    pts = O2 + others; assert len(pts) == 3 * k // 2 and (k // 4) * 4 == k
    cls = [[] for _ in range(6)]
    for idx, x in enumerate(O2): cls[idx % 6].append(x)        # spread O2 evenly
    it = iter(others)
    for q in range(6):
        while len(cls[q]) < k // 4: cls[q].append(next(it))
    classes = [kernel] + cls
    reqs = []
    for ln in LINES:
        Lset = [x for p in ln for x in classes[p]]
        if 0 in ln: S = [x for x in Lset if x not in O1]       # pencil line: request everything but the pool
        else: S = list(Lset)
        pad = [x for x in range(n) if x not in Lset and x not in O1]
        while len(S) < T: S.append(pad.pop())
        assert len(S) == T, (len(S), T)
        reqs.append((Lset, S))
    seven = [reply(S) for _, S in reqs]
    lines_ok = all(set(Lset) <= K for (Lset, _), K in zip(reqs, seven))
    cover = all(any(x in K and y in K for K in seven) for x in range(n) for y in range(x, n))
    print(f"  finite k: (k,T,n)=({k},{T},{n}) o={o} omega={om}: lines inside replies {lines_ok}; seven replies cover all pairs: {cover}")
    return cover


if __name__ == "__main__":
    for (t, N, o) in [(0.76, 1.82, 0.29), (0.76, 1.85, 0.305), (0.76, 1.9, 0.33), (0.76, 1.9, 0.40), (0.76, 1.82, 0.30), (0.76, 2.0, 0.38), (0.76, 2.1, 0.43)]:
        part1(t, N, o)
    for (t, N, o) in [("19/25", "91/50", "29/100"), ("19/25", "37/20", "61/200"), ("19/25", "19/10", "33/100"), ("19/25", "2", "19/50"), ("19/25", "21/10", "43/100")]:
        part2(t, N, o)
    for (k, T, n, o) in [(16, 12, 30, 5), (16, 13, 31, 5), (20, 16, 38, 6), (24, 19, 45, 7), (40, 31, 76, 13), (40, 31, 74, 12)]:
        part3(k, T, n, o)
