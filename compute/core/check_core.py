# CORE.md checks (exact, brute force on real sets).  py check_core.py
# A: Theorem T (triangle certificate)   B: Theorem Q (static quadrangle certificate)
# C: pool theorem (forcing by exhaustion) D: identities (waste, load sums)
import random, itertools
random.seed(644)

def pair_covered(V, Ks):
    """every pair {x,y} (x=y allowed) lies in a common co-edge  <=>  the complementary edges have no 2-cover"""
    for x in V:
        Ix = [K for K in Ks if x in K]
        if not Ix: return False
        for y in V:
            if y > x and not any(y in K for K in Ix): return False
    return True

def no_two_cover(V, Ks):
    Bs = [set(V) - K for K in Ks]
    for x in V:
        for y in V:
            if y >= x and all((x in B) or (y in B) for B in Bs): return False
    return True

def pad(S, V, c, avoid_first=None):
    """adversarial-ish reply: S plus random further points up to size c (prefers 'avoid_first' = useless points)"""
    S = set(S); rest = [v for v in V if v not in S]; random.shuffle(rest)
    if avoid_first is not None:
        rest.sort(key=lambda v: 0 if v in avoid_first else 1)
    return S | set(rest[:c - len(S)])

def cells(V, Ks):
    return {v: frozenset(i for i, K in enumerate(Ks) if v in K) for v in V}

def testA(trials=3000):
    ok = 0; used = 0
    for _ in range(trials):
        N = random.randint(8, 16); c = random.randint(3, N - 2); V = list(range(N))
        K = [set(random.sample(V, c)) for _ in range(3)]
        ty = cells(V, K)
        a  = {v for v in V if ty[v] == {0, 1}}; b = {v for v in V if ty[v] == {0, 2}}; d = {v for v in V if ty[v] == {1, 2}}
        e1 = {v for v in V if ty[v] == {0}};   e2 = {v for v in V if ty[v] == {1}};   e3 = {v for v in V if ty[v] == {2}}
        g  = {v for v in V if not ty[v]};      ka = {v for v in V if len(ty[v]) == 3}
        kap = list(ka); random.shuffle(kap); k4, k5, k6 = set(kap[0::3]), set(kap[1::3]), set(kap[2::3])
        S = [a | e3 | g | k4, b | e2 | g | k5, d | e1 | g | k6, e1 | e2 | e3]
        if max(len(s) for s in S) > c: continue
        used += 1
        Ks = K + [pad(s, V, c, avoid_first=ka) for s in S]
        assert pair_covered(V, Ks) and no_two_cover(V, Ks), (N, c, K)
        ok += 1
    print("A  Theorem T: %d instances, all uncoverable" % ok)

def testB(trials=3000):
    ok = 0
    for _ in range(trials):
        N = random.randint(8, 16); c = random.randint(3, N - 2); V = list(range(N))
        K = [set(random.sample(V, c)) for _ in range(4)]
        ty = cells(V, K)
        M = [({0, 1}, {2, 3}), ({0, 2}, {1, 3}), ({0, 3}, {1, 2})]
        S = [set(), set(), set()]
        for v in V:
            I = ty[v]
            if len(I) <= 1:
                for r in range(3): S[r].add(v)
            elif len(I) == 2:
                for r in range(3):
                    if I in (frozenset(M[r][0]), frozenset(M[r][1])): S[r].add(v)
            else:
                min(S, key=len).add(v)
        if max(len(s) for s in S) > c: continue
        Ks = K + [pad(s, V, c) for s in S]
        assert pair_covered(V, Ks) and no_two_cover(V, Ks), (N, c, K)
        # identity: sum of loads = 4k - N + u3 + 2 u4 + s1   (k = N - c)
        u3 = sum(1 for v in V if len(ty[v]) == 3); u4 = sum(1 for v in V if len(ty[v]) == 4)
        s1 = sum(1 for v in V if len(ty[v]) == 1)
        assert sum(len(s) for s in S) == 4 * (N - c) - N + u3 + 2 * u4 + s1
        ok += 1
    print("B  Theorem Q (static): %d instances, all uncoverable; load identity holds" % ok)

FANO = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]  # point 0 = o

def testC():
    res = []
    for (k, T, N, zeta) in [(8, 6, 16, 2), (8, 6, 16, 4), (8, 6, 15, 3), (12, 9, 24, 4), (12, 10, 24, 5),
                            (12, 10, 23, 3), (16, 13, 30, 4), (16, 13, 33, 5), (20, 16, 40, 6)]:
        c = N - k; om = c - T
        lo, hi = max(zeta, N - 2 * T), N - (3 * k + 1) // 2
        found = None
        # integer Fano weights: w0 in [lo,hi], lines through o <= c, other lines <= T
        for w0 in range(lo, hi + 1):
            rest = N - w0
            for w in itertools.product(range(0, c + 1), repeat=5):
                w6 = rest - sum(w)
                if w6 < 0: continue
                ws = (w0,) + w + (w6,)
                if all(sum(ws[p] for p in L) <= (c if 0 in L else T) for L in FANO):
                    found = ws; break
            if found: break
        if not found:
            res.append((k, T, N, zeta, "no integer weights")); continue
        V = list(range(N)); cls = {}; pos = 0
        for p in range(7):
            cls[p] = set(V[pos:pos + found[p]]); pos += found[p]
        wins = 0
        for trial in range(200):
            Z = set(random.sample(sorted(cls[0]), zeta))
            Ks = []
            for L in FANO:
                Lset = set().union(*[cls[p] for p in L])
                if 0 in L:
                    Zpp = set(random.sample(sorted(Z), om)); S = Lset - Zpp
                else:
                    S = set(Lset)
                # she pads her request to exactly T points (anything not in Zpp)
                extra = [v for v in V if v not in S and not (0 in L and v in Zpp)]; random.shuffle(extra)
                S |= set(extra[:T - len(S)])
                assert len(S) == T
                # pool adversary: additions inside Z \ S whenever there is room
                room = sorted(Z - S)
                if len(room) >= om: E = set(random.sample(room, om))
                else:
                    oth = [v for v in V if v not in S]; random.shuffle(oth); E = set(oth[:om])
                Ks.append(S | E)
            wins += pair_covered(V, Ks) and no_two_cover(V, Ks)
        res.append((k, T, N, zeta, found, "%d/200 wins" % wins))
    for r in res: print("C ", r)

def testD(trials=2000):
    # waste identity for arbitrary seven co-edges of size c on N points: sum_x (|I_x| - 3) = 7c - 3N
    for _ in range(trials):
        N = random.randint(7, 14); c = random.randint(2, N - 1); V = list(range(N))
        K = [set(random.sample(V, c)) for _ in range(7)]
        assert sum(sum(1 for S in K if v in S) - 3 for v in V) == 7 * c - 3 * N
    # Theorem T loads in closed form
    for _ in range(trials):
        N = random.randint(8, 16); c = random.randint(3, N - 2); V = list(range(N)); k = N - c
        K = [set(random.sample(V, c)) for _ in range(3)]
        if set.intersection(*K): continue
        a = len(K[0] & K[1]); b = len(K[0] & K[2]); d = len(K[1] & K[2])
        e3 = len(K[2] - K[0] - K[1]); g = N - len(K[0] | K[1] | K[2])
        assert a + e3 + g == 2 * a + 2 * k - N
        assert sum(len(K[i] - K[(i + 1) % 3] - K[(i + 2) % 3]) for i in range(3)) == 3 * c - 2 * (a + b + d)
    print("D  identities hold")

testA(); testB(); testC(); testD()
