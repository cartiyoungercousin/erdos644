# Rigid swap adversary (TWIN 18.6 F1 rule) against pencil-first with kernel N - 3k/2 (CORE 9.2).
# Seven requests, no discard, real sets, brute-force 2-cover test.   py swap_check.py
import random
random.seed(7)

def two_cover(V, Bs):
    for x in V:
        for y in V:
            if y >= x and all((x in B) or (y in B) for B in Bs): return (x, y)
    return None

def reply(V, S, k, order):
    """adversary: k points of V - S, taken in the priority order given (list of sets, then rest)"""
    avail = [v for v in V if v not in S]; random.shuffle(avail)
    def rank(v):
        for i, P in enumerate(order):
            if v in P: return i
        return len(order)
    avail.sort(key=rank)
    return set(avail[:k])

def play(k, T, N, late="random"):
    V = list(range(N)); c = N - k; om = c - T; osz = N - 3 * k // 2
    S1 = set(random.sample(V, T)); B1 = reply(V, S1, k, []); K1 = set(V) - B1
    # request 2: o2 (|o| - omega points of K1) + half of B1
    o2 = set(random.sample(sorted(K1), osz - om)); P2 = set(random.sample(sorted(B1), T - len(o2)))
    S2 = o2 | P2; assert len(S2) <= T
    unused = set(K1)
    B2 = reply(V, S2, k, [set(V) - unused])            # omit unused points: take used ones first
    K2 = set(V) - B2; o = K1 & K2
    # request 3: all of B1∩B2 and all of o except omega points
    g = B1 & B2; R = set(random.sample(sorted(o), max(0, len(o) + len(g) - T)))
    S3 = (o - R) | g
    if len(S3) > T: return "S3 too big"
    unused = K1 & K2
    B3 = reply(V, S3, k, [set(V) - unused])
    assert not (B1 & B2 & B3)
    # Theorem C finish on the anchors
    P12, P13, P23 = B1 & B2, B1 & B3, B2 & B3
    Q = [(B1 - B2 - B3), (B2 - B1 - B3), (B3 - B1 - B2)]
    S = {r: set() for r in (4, 5, 6, 7)}
    def split(P, ty):
        P = sorted(P); random.shuffle(P)
        for i, v in enumerate(P):
            for r in ty[i % len(ty)]: S[r].add(v)
    split(P12, [(4, 7), (5, 6)]); split(P13, [(4, 6), (5, 7)]); split(P23, [(4, 5), (6, 7)])
    split(Q[2], [(4, 5), (4, 6), (5, 7), (6, 7)])       # opposite P12
    split(Q[1], [(4, 5), (6, 7), (4, 7), (5, 6)])       # opposite P13
    split(Q[0], [(4, 6), (5, 7), (4, 7), (5, 6)])       # opposite P23
    if max(len(s) for s in S.values()) > T: return "finish too big %s" % [len(s) for s in S.values()]
    Bs = [B1, B2, B3]
    unused = set(V) - B1 - B2 - B3
    for r in (4, 5, 6, 7):
        if r == 4: order = [unused, B1 - B2 - B3]        # the swap: take unused first, then B1-only
        else: order = []
        Bs.append(reply(V, S[r], k, order))
    return two_cover(V, Bs)

for (k, T) in [(20, 16), (24, 19), (40, 31)]:
    for N in range(3 * T - k // 2 + 1, 3 * k - T):
        out = set()
        for _ in range(40): out.add(str(play(k, T, N)))
        print(k, T, N, "t=%.3f N/k=%.3f" % (T / k, N / k), "->", out)
