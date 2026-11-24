"""CORE 46, parts 4-5.  (4) scan of (N, o) with o >= 2 omega (rule well defined): which shape assignments are feasible (float LP).
(5) finite k, exact: integer design by MILP for one assignment, then the ACTUAL rule on real sets and brute-force pair cover."""
import itertools, sys
import highspy
from lpx import LP, INF
from frozen_antiplan import LINES, REG, feasible


def scan(t):
    eps = t - 0.75
    print("N, o, omega, #feasible/128, lexicographically-first feasible, PencilL+restH, allH, allL")
    worst = 128
    for N100 in range(181, 224, 3):
        N = N100 / 100; c = N - 1; om = c - t
        if not (5 * t - 2 < N < 3 - t): continue
        for o100 in range(int(200 * om) + 1, int(100 * c) + 1, 4):
            o = o100 / 100
            if o < 2 * om or 2 * (c - o) < 2 * om or N - 2 * c + o < 0: continue
            ok = [s for s in ("".join(x) for x in itertools.product("HL", repeat=7)) if feasible(t, N, o, s)]
            worst = min(worst, len(ok))
            print(f"{N:.2f} {o:.2f} {om:.2f} {len(ok):3d} {ok[0] if ok else '-------'} {'LLLHHHH' in ok} {'HHHHHHH' in ok} {'LLLLLLL' in ok}", flush=True)
    print("least number of feasible assignments over the scan:", worst)


def integer_design(k, T, n, o, shapes):
    c = n - k; om = c - T
    M = {"O1": om, "O2": o - om, "U1": om, "U2": 2 * (c - o) - om, "g": n - 2 * c + o}
    if min(M.values()) < 0: return None
    L = LP(); w = {(p, r): L.var(0, INF, 0.0, integer=True) for p in range(7) for r in REG}
    for r in REG: L.row([(w[p, r], 1.0) for p in range(7)], M[r], M[r])
    for i, ln in enumerate(LINES):
        tot = [(w[p, r], 1.0) for p in ln for r in REG]
        if shapes[i] == "H":
            L.row([(w[p, "O2"], 1.0) for p in ln], -INF, om - 1)                       # strictly fewer than omega requested in O
            L.row(tot + [(w[p, "O1"], -1.0) for p in ln], -INF, T)
        else:
            L.row(tot + [(w[p, "U1"], -1.0) for p in ln], -INF, T)
            L.row(tot + [(w[p, "U1"], -1.0) for p in ln] + [(w[p, r], -1.0) for p in ln for r in ("O1", "O2")], -INF, T - om)
    val, x = L.solve()
    if val is None: return None
    return {key: int(round(x[v])) for key, v in w.items()}


def real_check(k, T, n, o, shapes, w):
    c = n - k; om = c - T; u = 2 * (c - o)
    O = list(range(o)); U = list(range(o, o + u)); G = list(range(o + u, n))
    region = {"O1": O[:om], "O2": O[om:], "U1": U[:om], "U2": U[om:], "g": G}
    def reply(S):                                             # the adversary's rule, verbatim
        S = set(S); assert len(S) == T
        pool = O if len(S & set(O)) < om else U
        D = [x for x in pool if x not in S][:om]; assert len(D) == om
        return frozenset(S | set(D))
    classes = [[] for _ in range(7)]
    for r in REG:
        it = iter(region[r])
        for p in range(7):
            for _ in range(w[p, r]): classes[p].append(next(it))
    assert sorted(x for cl in classes for x in cl) == list(range(n))
    seven = []; inside = True
    for i, ln in enumerate(LINES):
        Lset = set(x for p in ln for x in classes[p])
        pool1 = set(region["O1"] if shapes[i] == "H" else region["U1"])
        S = Lset - pool1
        if shapes[i] == "L":
            for x in O:                                       # pad with O-points until at least omega of O are requested
                if len(S & set(O)) >= om: break
                S.add(x)
            padsrc = [x for x in range(n) if x not in S and x not in pool1]
        else:
            padsrc = [x for x in U + G if x not in S]
        for x in padsrc:
            if len(S) >= T: break
            S.add(x)
        assert len(S) == T, (len(S), T)
        K = reply(S); seven.append(K); inside &= Lset <= K
    cover = all(any(x in K and y in K for K in seven) for x in range(n) for y in range(x, n))
    return inside, cover


def finite(k, T, n, o, prefer=("LLLHHHH", "HHHHHHH", "LLLLLLL", "HHHLLLL")):
    cand = list(prefer) + ["".join(x) for x in itertools.product("HL", repeat=7)]
    for sh in cand:
        w = integer_design(k, T, n, o, sh)
        if w is None: continue
        inside, cover = real_check(k, T, n, o, sh, w)
        print(f"(k,T,n)=({k},{T},{n}) o={o} omega={n-k-T}: assignment {sh}: lines inside the actual replies {inside}; "
              f"the seven actual replies cover all pairs: {cover}", flush=True)
        return cover
    print(f"(k,T,n)=({k},{T},{n}) o={o}: NO integer design for any of the 128 assignments", flush=True)
    return None


if __name__ == "__main__":
    if sys.argv[1] == "scan": scan(float(sys.argv[2]))
    else:
        for (k, T, n, o) in [(40, 31, 74, 12), (40, 31, 76, 13), (40, 31, 80, 20), (100, 76, 182, 29), (100, 76, 185, 31), (100, 76, 190, 33),
                             (100, 76, 190, 40), (100, 76, 200, 50), (100, 76, 210, 70), (100, 76, 220, 90), (200, 151, 370, 60), (200, 151, 390, 80)]:
            finite(k, T, n, o)
