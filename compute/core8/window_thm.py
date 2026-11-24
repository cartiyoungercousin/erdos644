"""CORE 47: Theorem W (class-selected greedy rules lose when the selector is certified inside one pencil frame).
All checks are exact: the adversary's rule is applied verbatim to real sets and all pairs are checked.

(a) window / junta adversaries: a window W of B points, an ARBITRARY table {0,1}^B -> class (R classes), each class with its own
    random linear order on V; reply = S + first omega unrequested points in the order of the class of S & W.
(b) the twelve instances of 46.4 (threshold selector |S & O| < omega), by the threshold corollary (frame built by formula, no MILP).
"""
import itertools, random, sys

TRANS = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]          # which half (a=0 / b=1) of petals 1,2,3 each transversal takes


def finish(n, k, T, kernel, petals, Z, reply):
    """pencil requests L_i minus Z, four transversal requests; returns (pencil replies are the lines, all pairs covered)"""
    assert len(kernel) == n - 3 * k // 2 and all(len(p) == k // 2 for p in petals) and k % 4 == 0 and 4 * T >= 3 * k
    seven = []; exact = True
    for i in range(3):
        L = set(kernel) | set(petals[i]); S = L - set(Z); assert len(S) == T
        K = reply(S); seven.append(K); exact &= (K == frozenset(L))
    halves = [(p[:k // 4], p[k // 4:]) for p in petals]
    for tr in TRANS:
        S = set(x for i in range(3) for x in halves[i][tr[i]])
        for x in range(n):
            if len(S) >= T: break
            S.add(x)
        seven.append(reply(S))
    cover = all(any(x in K and y in K for K in seven) for x in range(n) for y in range(x, n))
    return exact, cover


def junta_trial(n, k, T, B, R, rng):
    om = n - k - T
    W = rng.sample(range(n), B)
    table = {}                                                 # lazily random: arbitrary function of the trace on W
    orders = [rng.sample(range(n), n) for _ in range(R)]
    def cls(S):
        key = tuple(x in S for x in W)
        if key not in table: table[key] = rng.randrange(R)
        return table[key]
    def reply(S):
        S = set(S); assert len(S) == T
        D = [x for x in orders[cls(S)] if x not in S][:om]
        return frozenset(S | set(D))
    r = cls(set(W))                                            # the class when the whole window is requested
    Z = [x for x in orders[r] if x not in W][:om]
    kernel = list(W) + Z
    rest = [x for x in range(n) if x not in kernel]; rng.shuffle(rest)
    need = n - 3 * k // 2 - len(kernel); assert need >= 0
    kernel += rest[:need]; rest = rest[need:]
    petals = [rest[i * (k // 2):(i + 1) * (k // 2)] for i in range(3)]
    return finish(n, k, T, kernel, petals, Z, reply)


def threshold_instance(k, T, n, o):
    """46's rule; L-frame: Z = U1, x = min(omega, T - k/2) points of O in the kernel, omega - x further points of O in every petal"""
    c = n - k; om = c - T; u = 2 * (c - o)
    O = list(range(o)); U = list(range(o, o + u)); G = list(range(o + u, n))
    def reply(S):
        S = set(S); assert len(S) == T
        pool = O if len(S & set(O)) < om else U
        D = [x for x in pool if x not in S][:om]; assert len(D) == om
        return frozenset(S | set(D))
    x = min(om, T - k // 2); y = om - x
    if x + 3 * y > o: return None
    Z = U[:om]; Oit = iter(O)
    kernel = Z + [next(Oit) for _ in range(x)]
    petals = [[next(Oit) for _ in range(y)] for _ in range(3)]
    rest = [p for p in O + U + G if p not in kernel and all(p not in q for q in petals)]
    need = n - 3 * k // 2 - len(kernel); kernel += rest[:need]; rest = rest[need:]
    for q in petals:
        m = k // 2 - len(q); q += rest[:m]; rest = rest[m:]
    return finish(n, k, T, kernel, petals, Z, reply)


if __name__ == "__main__":
    rng = random.Random(47)
    print("(a) junta / window adversaries, arbitrary class table, class-dependent random orders")
    for (k, T, n) in [(40, 31, 74), (40, 31, 80), (100, 76, 185), (100, 76, 190), (100, 76, 210)]:
        Bmax = T - k // 2
        for B in sorted({1, 3, Bmax // 2, Bmax}):
            for R in (2, 8, 64):
                res = [junta_trial(n, k, T, B, R, rng) for _ in range(20)]
                print(f"  (k,T,n)=({k},{T},{n}) B={B} (T-k/2={Bmax}) R={R}: 20 random adversaries, "
                      f"pencil replies exact {sum(e for e, _ in res)}/20, good seven {sum(c for _, c in res)}/20", flush=True)
    print("(b) the instances of 46.4, threshold corollary (needs o >= 3 omega - 2 min(omega, T - k/2))")
    for (k, T, n, o) in [(40, 31, 74, 12), (40, 31, 76, 13), (40, 31, 80, 20), (100, 76, 182, 29), (100, 76, 185, 31), (100, 76, 190, 33),
                         (100, 76, 190, 40), (100, 76, 200, 50), (100, 76, 210, 70), (100, 76, 220, 90), (200, 151, 370, 60), (200, 151, 390, 80)]:
        om = n - k - T; cond = o >= 3 * om - 2 * min(om, T - k // 2)
        r = threshold_instance(k, T, n, o)
        print(f"  (k,T,n,o)=({k},{T},{n},{o}) omega={om}: hypothesis {cond}; pencil replies exact {r[0] if r else None}, good seven {r[1] if r else None}", flush=True)
