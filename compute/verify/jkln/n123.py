"""PETAL 12.3: the 4+3 arena-aware requester vs ANY adversary of the family (colour c: >= k-dk points in V_c minus S,
the remaining dk points anywhere outside S, including outside both arenas).  delta < t/8.
Interpretation used by the requester: 'V_F-parts' of earlier replies = all their points outside V_A (so outside-arena
leaks are also requested).  Checks budgets (never clipped) and the final exact 2-cover test of the seven replies."""
import random, sys, itertools


def no2cover(sets):
    mask = {}
    for j, s in enumerate(sets):
        for x in s: mask[x] = mask.get(x, 0) | (1 << j)
    ms = sorted(set(mask.values())); full = (1 << len(sets)) - 1
    for i in range(len(ms)):
        for j in range(i, len(ms)):
            if ms[i] | ms[j] == full: return False
    return True


def run(k, T, dk, seed, leak):
    rnd = random.Random(seed)
    n = int(round(k * (1 + T / (2 * k)) - dk))          # arena size (1 + t/2 - delta) k
    A = list(range(n)); F = list(range(n, 2 * n)); O = list(range(2 * n, 2 * n + (3 * k if leak == 'outside' else 0)))
    reps = []
    e = 1

    def adversary(S, prefer):
        S = set(S)
        opts = []
        for name, V in (("A", A), ("F", F)):
            free = [x for x in V if x not in S]
            if len(free) >= k - dk: opts.append((name, free))
        assert opts, "adversary stuck (not a legal state)"
        name, free = rnd.choice(opts)
        own = set(rnd.sample(free, k - dk))
        # leak: dk points anywhere outside S and own
        pool = [x for x in A + F + O if x not in S and x not in own]
        if leak == "reuse" and reps:
            cnt = {}
            for r in reps:
                for x in r:
                    if x in pool_set(pool): cnt[x] = cnt.get(x, 0) + 1
            order = sorted(cnt, key=lambda x: -cnt[x])
            lk = set(order[:dk])
            if len(lk) < dk: lk |= set(rnd.sample([x for x in pool if x not in lk], dk - len(lk)))
        elif leak == "outside":
            lk = set(rnd.sample([x for x in O if x not in S], dk))
        else:
            lk = set(rnd.sample(pool, dk))
        return name, own | lk

    def pool_set(pool):
        return set(pool)

    # requests 1-4
    covered = 0
    block = (T - (T // 2 + e))
    Ablocks = [A[i * block:(i + 1) * block] for i in range(4)]
    assert sum(len(b) for b in Ablocks) >= n, "cannot cover V_A"
    cols = []
    for j in range(4):
        nonA = set()
        for r in reps: nonA |= {x for x in r if x >= n}
        req_nonA = set(nonA)
        need = T // 2 + e
        assert len(req_nonA) <= need, ("earlier non-A parts do not fit", len(req_nonA), need)
        extra = [x for x in F if x not in req_nonA]
        req_nonA |= set(rnd.sample(extra, need - len(req_nonA)))
        S = req_nonA | set(Ablocks[j])
        assert len(S) <= T, ("request too big", len(S), T)
        name, r = adversary(S, None)
        assert name == "A", "reply not of colour A"
        reps.append(frozenset(r)); cols.append(name)
    petals = list(reps)
    common = set(petals[0])
    for p in petals[1:]: common &= p
    assert not common, "petals have a common point"
    U = set().union(*petals)
    Utail = {x for x in U if x >= n}
    Z = []
    cents = []
    for j in range(3):
        Zprev = set().union(*Z) if Z else set()
        S = set(Utail)
        S |= {x for x in Zprev if x < n}        # centres' V_A parts
        need = T // 2 + e
        Apart = set(x for x in S if x < n)
        if len(Apart) < need:
            Apart |= set(rnd.sample([x for x in A if x not in Apart], need - len(Apart)))
        S = Utail | Apart
        assert len(S) <= T, ("centre request too big", j, len(S), T)
        name, r = adversary(S, None)
        assert name == "F", "centre reply not of colour F"
        reps.append(frozenset(r)); cents.append(r)
        Z.append(set(r) & U)
    for i in range(3):
        for j in range(i):
            assert not (Z[i] & Z[j]), "traces not disjoint"
    return no2cover(reps)


if __name__ == "__main__":
    k, T = 120, 90                      # t = 3/4, t/8 k = 11.25
    tot = bad = 0
    for dk in (0, 5, 9, 11):
        for leak in ("rand", "reuse") + (("outside",) if len(sys.argv) > 1 else ()):
            ok = 0; err = 0
            for s in range(150):
                try:
                    ok += run(k, T, dk, s, leak); tot += 1
                except AssertionError as ex:
                    err += 1
                    if err <= 2: print("  assertion:", dk, leak, ex)
            print("dk=%d leak=%s: seven-reply uncoverable in %d/150, assertion failures %d" % (dk, leak, ok, err), flush=True)
