"""CORE Part IX (44): the 'least request-dependent' stationary rule -- one bit of the request's trace on a second cell
selects the in-cell order.  Cells O (ordered), U = A + B (ordered, A first), g = gL + gR.
  if |S & O| < omega : bit = [|S & A| >= |S & B|];  dump = first omega unrequested points of O, forward order if bit else backward
  else               : bit = [|S & gL| >= |S & gR|]; dump = first omega unrequested points of U, forward order if bit else backward
Pools: O^1 = first omega of O, O^0 = last omega of O, U^1 = first omega of U (in A), U^0 = last omega of U (in B).
Test (as CORE 46): a pencil of three lines of ONE shape X in {H1, H0, L1, L0} through a kernel class containing the pool of
X, four transversal lines of mass <= T (their replies are irrelevant).  Integer design by MILP; then the rule is applied
VERBATIM to real sets and all pairs are checked by brute force.  Usage: py onebit.py"""
import sys, itertools
sys.path.insert(0, "../core8")
from lpx import LP, INF

LINES = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
REG = ["O1", "Om", "O0", "U1", "Am", "Bm", "U0", "gL", "gR"]


def sizes(k, T, n, o):
    c = n - k; om = c - T; a = c - o; g = n - 2 * c + o
    M = {"O1": om, "Om": o - 2 * om, "O0": om, "U1": om, "Am": a - om, "Bm": a - om, "U0": om, "gL": g // 2, "gR": g - g // 2}
    return None if min(M.values()) < 0 else M


def design(k, T, n, o, X):
    c = n - k; om = c - T; M = sizes(k, T, n, o)
    if M is None: return None
    L = LP(); w = {(p, r): L.var(0, INF, 0.0, integer=True) for p in range(7) for r in REG}
    for r in REG: L.row([(w[p, r], 1.0) for p in range(7)], M[r], M[r])
    pool = {"H1": "O1", "H0": "O0", "L1": "U1", "L0": "U0"}[X]
    L.row([(w[0, pool], 1.0)], M[pool], M[pool])                                  # the pool lies in the kernel class
    def S(ln, regs, coef=1.0): return [(w[p, r], coef) for p in ln for r in regs if r != pool]
    for i, ln in enumerate(LINES):
        if i >= 3:
            L.row([(w[p, r], 1.0) for p in ln for r in REG], -INF, T); continue
        L.row(S(ln, REG), -INF, T)                                                # |L minus pool| <= T
        A, B = ["U1", "Am"], ["Bm", "U0"]; Oall = ["O1", "Om", "O0"]
        if X[0] == "H":
            # worst case after padding is controlled in real_check; here: fewer than omega of O requested, and the bit
            L.row(S(ln, Oall), -INF, om - 1)
            if X[1] == "1": L.row(S(ln, A) + S(ln, B, -1.0), 0, INF)
            else: L.row(S(ln, A) + S(ln, B, -1.0), -INF, -1)
        else:
            # at least omega of O requested, possibly after padding: |L minus pool| + (omega - |L & O|)^+ <= T
            L.row(S(ln, REG) + S(ln, Oall, -1.0), -INF, T - om)
            if X[1] == "1": L.row(S(ln, ["gL"]) + S(ln, ["gR"], -1.0), 0, INF)
            else: L.row(S(ln, ["gL"]) + S(ln, ["gR"], -1.0), -INF, -1)
    val, x = L.solve()
    if val is None: return None
    return {key: int(round(x[v])) for key, v in w.items()}


def real_check(k, T, n, o, X, w):
    c = n - k; om = c - T; M = sizes(k, T, n, o)
    pts = iter(range(n)); region = {r: [next(pts) for _ in range(M[r])] for r in REG}
    O = region["O1"] + region["Om"] + region["O0"]; A = region["U1"] + region["Am"]; B = region["Bm"] + region["U0"]
    U = A + B; gL, gR = region["gL"], region["gR"]
    sO, sA, sB, sgL, sgR = map(set, (O, A, B, gL, gR))
    def reply(S):                                                                 # the adversary's rule, verbatim
        S = set(S); assert len(S) == T
        if len(S & sO) < om:
            bit = len(S & sA) >= len(S & sB); cell = O if bit else O[::-1]
        else:
            bit = len(S & sgL) >= len(S & sgR); cell = U if bit else U[::-1]
        D = [x for x in cell if x not in S][:om]; assert len(D) == om
        return frozenset(S | set(D))
    classes = [[] for _ in range(7)]
    for r in REG:
        it = iter(region[r])
        for p in range(7):
            for _ in range(w[p, r]): classes[p].append(next(it))
    assert sorted(x for cl in classes for x in cl) == list(range(n))
    pool = set(region[{"H1": "O1", "H0": "O0", "L1": "U1", "L0": "U0"}[X]])
    seven = []; inside = True
    for i, ln in enumerate(LINES):
        Lset = set(x for p in ln for x in classes[p])
        if i >= 3:
            S = set(Lset); pad = [x for x in range(n) if x not in S]
        else:
            S = Lset - pool
            if X[0] == "H":
                pad = gL + gR + (A if X[1] == "1" else B)                         # keeps |S & O| and the bit
            else:
                first = []
                for x in O:
                    if len((S | set(first)) & sO) >= om: break
                    if x not in S: first.append(x)
                pad = first + O + U + (gL if X[1] == "1" else gR)
            pad = [x for x in pad if x not in S and x not in pool]
        for x in pad:
            if len(S) >= T: break
            S.add(x)
        if len(S) != T: return None, None
        K = reply(S); seven.append(K)
        if i < 3: inside &= Lset <= K
    cover = all(any(x in K and y in K for K in seven) for x in range(n) for y in range(x, n))
    return inside, cover


if __name__ == "__main__":
    inst = [(40, 31, 74, 12), (40, 31, 76, 13), (40, 31, 80, 20), (100, 76, 182, 29), (100, 76, 185, 31), (100, 76, 190, 33), (100, 76, 190, 40),
            (100, 76, 200, 50), (100, 76, 210, 70), (100, 76, 220, 90), (200, 151, 370, 60), (200, 151, 390, 80)]
    inst += [(100, 76, n, o) for n in range(181, 224, 3) for o in range(2 * (n - 176), n - 100, 6) if 2 * (n - 100 - o) >= 2 * (n - 176) and n - 2 * (n - 100) + o >= 0]
    bad = 0
    for (k, T, n, o) in inst:
        res = {}
        for X in ("L1", "L0", "H1", "H0"):
            w = design(k, T, n, o, X)
            if w is None: res[X] = "-"; continue
            inside, cover = real_check(k, T, n, o, X, w)
            res[X] = "GOOD7" if (inside and cover) else f"design-but-fail({inside},{cover})"
        ok = any(v == "GOOD7" for v in res.values()); bad += not ok
        print(f"(k,T,n,o)=({k},{T},{n},{o}) omega={n-k-T}: {res}  {'' if ok else '<<< NO PENCIL OF ONE SHAPE'}", flush=True)
    print("instances:", len(inst), "without a one-shape pencil:", bad)
