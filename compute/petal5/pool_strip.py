"""PETAL §26: pooled arena adversary A(t, delta) in the strip 7/5 - 17t/10 <= delta < t/6, t > 3/4.

Written from the statements (PETAL §1, §12, §20.2, §23.2); imports nothing from compute/verify or compute/petal3.

Fixed family H(k; nA, nF, dA, dF, m):
  ground set = R_A (nA points) + R_F (nF points) + pool O (m points);
  class c member = k-set with >= k - d_c points in R_c (the rest anywhere: own arena, other arena, pool).
  Variant 'pool-only': the rest only in R_c or O (no cross-arena leak).
Game: request S, |S| <= T; reply = member avoiding S (the adversary chooses).  Win = seven replies with no 2-point cover.

Strategy PS (pooled sealing) = AP's skeleton (23.2), forced branch, with direct accounting:
  petals (4 requests): tau_Y points of R_Y (forces class X) containing I cap R_Y, plus min(b, |I minus R_Y|) points of
      I minus R_Y, b = T - tau_Y, I = common intersection of the petals so far (pool points included);
  centres (3 requests): G_j in R_X of size max(tau_X, |Z_<j cap R_X|) containing Z_<j cap R_X, plus B minus B_j,
      B = union of the petals' points outside R_X (other arena AND pool), B_0, B_1, B_2 a near-equal split.
"""
import itertools, random, sys


class Fam:
    def __init__(s, k, nA, nF, dA, dF, m, pool_only=False):
        s.k, s.n, s.d, s.m, s.po = k, [nA, nF], [dA, dF], m, pool_only
        s.N = nA + nF + m
        s.R = [set(range(nA)), set(range(nA, nA + nF)), set(range(nA + nF, s.N))]
        s.reg = [0] * nA + [1] * nF + [2] * m
        s.ALL = set(range(s.N))

    def allowed_rest(s, c):  # where the leak of a class-c member may go
        return s.R[c] | s.R[2] if s.po else s.ALL

    def classes(s, E):
        out = []
        for c in (0, 1):
            if len(E & s.R[c]) >= s.k - s.d[c] and (not s.po or E <= s.allowed_rest(c)):
                out.append(c)
        return out

    def feasible(s, S, c):
        return len(s.R[c] - S) >= s.k - s.d[c] and len(s.allowed_rest(c) - S) >= s.k

    def tau_c(s, c):  # in points, by the direct count [proved by hand]; checked by tau_exact
        return s.n[c] - s.k + s.d[c] + 1


def tau_profile(F):
    """exact tau(H): H is invariant under Sym(R_A) x Sym(R_F) x Sym(O), and 'some member avoids S' depends only on
    (|S cap R_A|, |S cap R_F|, |S cap O|).  So tau = least a+f+o over profiles that no member avoids."""
    best = None
    for a in range(F.n[0] + 1):
        for f in range(F.n[1] + 1):
            for o in range(F.m + 1):
                free = [F.n[0] - a, F.n[1] - f, F.m - o]
                ok = False
                for c in (0, 1):
                    room = free[c] + free[2] + (0 if F.po else free[1 - c])
                    if free[c] >= F.k - F.d[c] and room >= F.k:
                        ok = True
                if not ok and (best is None or a + f + o < best):
                    best = a + f + o
    return best


def tau_exact(F):
    """exact tau(H) by cut generation: ILP over a growing member list, oracle = definition of membership."""
    import highspy, numpy as np
    cuts = []
    while True:
        h = highspy.Highs(); h.setOptionValue("output_flag", False)
        N = F.N
        for _ in range(N):
            h.addVar(0, 1)
        h.changeColsCost(N, np.arange(N, dtype=np.int32), np.ones(N))
        h.changeColsIntegrality(N, np.arange(N, dtype=np.int32), np.array([1] * N, dtype=np.uint8))
        for E in cuts:
            idx = np.array(sorted(E), dtype=np.int32)
            h.addRow(1, highspy.kHighsInf, len(idx), idx, np.ones(len(idx)))
        h.run()
        x = h.getSolution().col_value
        S = {i for i in range(N) if x[i] > 0.5}
        E = None
        for c in (0, 1):
            if F.feasible(S, c):
                own = sorted(F.R[c] - S)
                rest = sorted((F.allowed_rest(c) - S) - set(own))
                E = set(own[:F.k]) | set(rest[:max(0, F.k - len(own))])
                if len(E) < F.k:
                    E = None
                    continue
                break
        if E is None:
            return len(S), S
        cuts.append(E)


# ---------------- independent brute-force 2-cover test ----------------
def two_cover(sets):
    """returns a pair (x, y) of points (x == y allowed) meeting every set, or None.  Plain double loop over points."""
    U = sorted(set().union(*sets))
    for i, x in enumerate(U):
        for y in U[i:]:
            if all((x in E) or (y in E) for E in sets):
                return (x, y)
    return None


# ---------------- strategy PS ----------------
def split3(B):
    B = sorted(B)
    q, r = divmod(len(B), 3)
    sizes = [q + (1 if i < r else 0) for i in range(3)]
    out, p = [], 0
    for sz in sizes:
        out.append(set(B[p:p + sz])); p += sz
    return out


def ps_strategy(F, T, ask, X):
    Y = 1 - X
    k = F.k
    tX, tY = F.tau_c(X), F.tau_c(Y)
    reqs, reps, flags = [], [], []
    b = T - tY
    # ---- petals
    petals = []
    I = None
    for i in range(4):
        RY = sorted(F.R[Y])
        S = set()
        inner = set() if I is None else I
        S |= inner & F.R[Y]
        for x in RY:
            if len(S) >= tY: break
            S.add(x)
        rest = sorted(inner - F.R[Y])
        S |= set(rest[:b])
        if i == 3 and len(rest) > b: flags.append("RI overflow")
        # fill up to T inside R_X (harmless; makes the request maximal)
        for x in sorted(F.R[X]):
            if len(S) >= T: break
            S.add(x)
        reqs.append(S)
        E = ask(S)
        if E is None: flags.append("no reply"); return dict(reqs=reqs, reps=reps, flags=flags)
        assert not (E & S) and len(E) == k
        if F.classes(E) != [X]: flags.append("petal class")
        petals.append(E); reps.append(E)
        I = set(E) if I is None else I & E
    if I: flags.append("petals meet")
    U = set().union(*petals)
    B = U - F.R[X]
    Bs = split3(B)
    Z = []
    for j in range(3):
        prev = set().union(*Z) & F.R[X] if Z else set()
        G = set(prev)
        for x in sorted(F.R[X]):
            if len(G) >= tX: break
            G.add(x)
        S = G | (B - Bs[j])
        reqs.append(S)
        E = ask(S)
        if E is None: flags.append("no reply"); return dict(reqs=reqs, reps=reps, flags=flags)
        assert not (E & S) and len(E) == k
        if F.classes(E) != [Y]: flags.append("centre class")
        Z.append(E & U); reps.append(E)
    for a, c in itertools.combinations(range(3), 2):
        if Z[a] & Z[c]: flags.append("traces meet")
    return dict(reqs=reqs, reps=reps, flags=flags)


def ps_cost_bound(F, T, X):
    """predicted worst request size (points)."""
    Y = 1 - X
    B = 4 * F.d[X]
    return max(F.tau_c(X), 2 * F.d[Y]) + B - B // 3


# ---------------- adversary: parametrised by a genome, hill-climbed ----------------
FEAT = 7


def rand_gene(rnd):
    return dict(w=[rnd.uniform(-3, 3) for _ in range(FEAT)], wl=[rnd.uniform(-3, 3) for _ in range(FEAT)],
                extra=rnd.choice([0, 0, 0, 1, 2]), seed=rnd.randrange(10 ** 9), cpref=rnd.choice([0, 1, 2]))


class Adv:
    def __init__(s, F, genome):
        s.F, s.g, s.reps, s.cls, s.reqs = F, genome, [], [], []

    def feats(s, x, c, S):
        F = s.F
        cnt = sum(1 for E in s.reps if x in E)
        cntc = sum(1 for E, cc in zip(s.reps, s.cls) if cc == c and x in E)
        inall = 1 if s.reps and all(x in E for E in s.reps if True) else 0
        inallc = 1 if any(cc == c for cc in s.cls) and all(x in E for E, cc in zip(s.reps, s.cls) if cc == c) else 0
        reqd = sum(1 for R in s.reqs if x in R)
        return [cnt, cntc, inall, inallc, reqd, 1 if F.reg[x] == 2 else 0, 1 if F.reg[x] == 1 - c else 0]

    def reply(s, S):
        F, k = s.F, s.F.k
        gi = s.g[min(len(s.reps), len(s.g) - 1)]
        rnd = random.Random(gi["seed"])
        fc = [c for c in (0, 1) if F.feasible(S, c)]
        if not fc: return None
        c = fc[0] if len(fc) == 1 else (fc[gi["cpref"]] if gi["cpref"] < 2 else rnd.choice(fc))
        sc = {x: sum(a * f for a, f in zip(gi["w"], s.feats(x, c, S))) + 0.01 * rnd.random() for x in F.ALL - S}
        sl = {x: sum(a * f for a, f in zip(gi["wl"], s.feats(x, c, S))) + 0.01 * rnd.random() for x in F.ALL - S}
        own_n = k - F.d[c] + min(gi["extra"], F.d[c])
        own = sorted(F.R[c] - S, key=lambda x: -sc[x])[:own_n]
        E = set(own)
        rest = sorted((F.allowed_rest(c) - S) - E, key=lambda x: -sl[x])
        E |= set(rest[:k - len(E)])
        assert len(E) == k
        s.reps.append(E); s.cls.append(c); s.reqs.append(set(S))
        return E


def play(F, T, X, genome, strat=None):
    adv = Adv(F, genome)
    out = (strat or ps_strategy)(F, T, adv.reply, X)
    reps = out["reps"]
    mr = max(len(R) for R in out["reqs"])
    out["cmax"] = max((len(R) for R in out["reqs"][4:]), default=0)
    cov = two_cover(reps) if len(reps) == 7 else "short"
    return out, mr, cov


def score(F, reps):
    """adversary objective: max number of the seven replies covered by two points."""
    U = sorted(set().union(*reps))
    best = 0
    for i, x in enumerate(U):
        for y in U[i:]:
            best = max(best, sum(1 for E in reps if x in E or y in E))
    return best


def search(F, T, X, games, seed, strat=None):
    rnd = random.Random(seed)
    st = dict(games=0, covers=0, viol=0, flags=set(), maxreq=0, maxcov=0, cmax=0)

    def ev(g):
        out, mr, cov = play(F, T, X, g, strat)
        st["games"] += 1
        st["maxreq"] = max(st["maxreq"], mr)
        st["cmax"] = max(st["cmax"], out["cmax"])
        if mr > T: st["viol"] += 1
        if cov not in (None, "short"): st["covers"] += 1
        st["flags"] |= set(out["flags"])
        sc = score(F, out["reps"]) if len(out["reps"]) == 7 else 8
        st["maxcov"] = max(st["maxcov"], sc)
        return sc * 1000 + mr

    pop = [[rand_gene(rnd) for _ in range(7)] for _ in range(games // 2 - 3)]
    # hand-made extremes: petals leak into fresh pool / other-arena points (max |B|); centres put own part and leak on
    # points of earlier replies (max traces on U)
    fresh = dict(w=[1, 1, 3, 3, 0, 0, 0], wl=[-5, -5, 0, 0, 0, 3, 0], extra=0, seed=1, cpref=0)
    freshF = dict(fresh, wl=[-5, -5, 0, 0, 0, 0, 3])
    hit = dict(w=[3, 0, 0, 0, 0, 0, 0], wl=[5, 0, 2, 0, 0, 0, 0], extra=0, seed=2, cpref=0)
    pop += [[fresh] * 4 + [hit] * 3, [freshF] * 4 + [hit] * 3, [dict(fresh, wl=[-5, -5, 0, 0, 0, 1, 1])] * 4 + [hit] * 3]
    scored = sorted(((ev(g), i, g) for i, g in enumerate(pop)), key=lambda z: -z[0])[:6]
    for it in range(games - games // 2):
        _, _, g = rnd.choice(scored)
        g2 = [dict(x, w=list(x["w"]), wl=list(x["wl"])) for x in g]
        j = rnd.randrange(7)
        g2[j] = rand_gene(rnd) if rnd.random() < 0.3 else dict(g2[j], w=[a + rnd.gauss(0, 1) for a in g2[j]["w"]],
                                                               wl=[a + rnd.gauss(0, 1) for a in g2[j]["wl"]],
                                                               seed=rnd.randrange(10 ** 9))
        scored.append((ev(g2), 10 ** 6 + it, g2))
        scored = sorted(scored, key=lambda z: -z[0])[:6]
    return st


if __name__ == "__main__":
    pass
