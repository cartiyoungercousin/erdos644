"""Independent verifier for CORE 46 (frozen anti-plan) and 47 (Theorem W). Finite k, rule applied verbatim."""
import random, itertools, sys, functools


@functools.lru_cache(None)
def plan(k, T):
    """pencil frame at finite k: |kappa| = n - dk, petals p_i, classes (a_i,b_i); transversals <= T."""
    dk = (3 * k + 1) // 2
    ps = [(k + 1) // 2] * 2 + [k // 2] if k % 2 else [k // 2] * 3
    for a1 in range(ps[0] + 1):
        for a2 in range(ps[1] + 1):
            for a3 in range(ps[2] + 1):
                A = [(a1, ps[0] - a1), (a2, ps[1] - a2), (a3, ps[2] - a3)]
                for coset in (0, 1):
                    tr = [sum(A[i][bits[i]] for i in range(3))
                          for bits in itertools.product((0, 1), repeat=3) if sum(bits) % 2 == coset]
                    if max(tr) <= T:
                        return dk, A, coset
    return None


def fano_lines(coset):
    return [b for b in itertools.product((0, 1), repeat=3) if sum(b) % 2 == coset]


def cover_ok(n, Ks):
    types = set()
    for x in range(n):
        m = 0
        for i, K in enumerate(Ks):
            if x in K:
                m |= 1 << i
        types.add(m)
    ts = list(types)
    return all(a & b for a in ts for b in ts), ts


def build_classes(n, kernel, rng, A):
    rest = [x for x in range(n) if x not in kernel]
    rng.shuffle(rest)
    classes = []
    pos = 0
    for i in range(3):
        a = rest[pos:pos + A[i][0]]; pos += A[i][0]
        b = rest[pos:pos + A[i][1]]; pos += A[i][1]
        classes.append((set(a), set(b)))
    assert pos == len(rest)
    return classes


def make_reply(n, k, sigma, order_of):
    def reply(S):
        S = set(S)
        rr = sigma(frozenset(S))
        d = n - k - len(S)
        add = [x for x in order_of(rr) if x not in S][:d]
        return S | set(add)
    return reply


def finish(n, k, T, kernel, Z, W, reply, rng, A, coset, evil):
    classes = build_classes(n, kernel, rng, A)
    Ks = []
    for i in range(3):
        L = kernel | classes[i][0] | classes[i][1]
        assert len(L) <= n - k
        S = L - set(Z)
        assert len(S) <= T and set(W) <= S
        K = reply(S)
        if not L <= K:
            return ('FAIL_pencil', i)
        Ks.append(K)
    for bits in fano_lines(coset):
        L = set()
        for i in range(3):
            L |= classes[i][bits[i]]
        assert len(L) <= T
        if evil:
            pool = [x for x in range(n) if x not in L]; rng.shuffle(pool)
            K = L | set(pool[:n - k - len(L)])
        else:
            K = reply(L)
        if not L <= K:
            return ('FAIL_tr',)
        Ks.append(K)
    assert all(len(K) == n - k for K in Ks)
    ok, ts = cover_ok(n, Ks)
    return 'OK' if ok else ('FAIL_cover', ts)


def run_window(n, k, T, W, sigma, order_of, rng, evil=False, fill='random'):
    pl = plan(k, T)
    if pl is None:
        return 'noplan'
    dk, A, coset = pl
    kap = n - dk
    omega = n - k - T
    Wset = set(W)
    if len(W) + omega > kap:
        return 'window_too_big'
    r = sigma(frozenset(Wset))
    ordr = order_of(r)
    Z = [x for x in ordr if x not in Wset][:omega]
    kernel = set(Wset) | set(Z)
    if fill == 'early':
        cand = [x for x in ordr if x not in kernel]
    elif fill == 'late':
        cand = [x for x in reversed(ordr) if x not in kernel]
    else:
        cand = [x for x in range(n) if x not in kernel]; rng.shuffle(cand)
    kernel |= set(cand[:kap - len(kernel)])
    return finish(n, k, T, kernel, Z, W, make_reply(n, k, sigma, order_of), rng, A, coset, evil)


def make_adv(n, W, kind, rng):
    Wl = sorted(W)
    V = list(range(n))
    Ws = set(Wl)
    cache = {}
    if kind == 'table':
        R = rng.choice([2, 8, 64]); tab = {}; seed = rng.randrange(10**9)

        def sigma(S):
            key = tuple(x in S for x in Wl)
            if key not in tab:
                tab[key] = rng.randrange(R)
            return tab[key]

        def order_of(r):
            if r not in cache:
                o = V[:]; random.Random(seed + r).shuffle(o); cache[r] = o
            return cache[r]
        return sigma, order_of
    if kind == 'parity_headW':
        def sigma(S): return sum(x in S for x in Wl) % 2

        def order_of(r):
            rest = [x for x in V if x not in Ws]
            if r: rest.reverse()
            return Wl[::(1 if r else -1)] + rest
        return sigma, order_of
    if kind == 'hash_tied':
        def sigma(S):
            h = 0
            for x in Wl:
                h = (h * 1000003 + (x in S) + 7 * x) % (2**31 - 1)
            return h % 5

        def order_of(r):
            if not Wl:
                return V[:]
            return sorted(V, key=lambda x: (min(abs(x - w) for w in Wl) * (1 if r % 2 else -1), (x * 31 + r) % 97, x))
        return sigma, order_of
    if kind == 'head_interleave':
        def sigma(S): return sum(i * (x in S) for i, x in enumerate(Wl)) % 3

        def order_of(r):
            rest = [x for x in V if x not in Ws]; random.Random(r).shuffle(rest)
            o = []
            for i in range(max(len(rest), len(Wl))):
                if i < len(rest): o.append(rest[i])
                if i < len(Wl): o.append(Wl[(i + r) % len(Wl)])
            return list(dict.fromkeys(o))
        return sigma, order_of
    if kind == 'maj':
        def sigma(S): return int(2 * sum(x in S for x in Wl) > len(Wl))

        def order_of(r):
            rest = [x for x in V if x not in Ws]
            return (Wl + rest) if r else (rest[::-1] + Wl)
        return sigma, order_of
    raise ValueError(kind)


def main():
    rng = random.Random(12345)
    tot = {}; fails = []
    kinds = ['table', 'parity_headW', 'hash_tied', 'head_interleave', 'maj']
    for k in list(range(4, 31)) + [40]:
        Tmin = -(-3 * k // 4)
        for T in sorted({Tmin, Tmin + 1, Tmin + 3}):
            for n in sorted({k + T, k + T + 1, k + T + 3, k + T + 7, int(1.9 * k), int(2.1 * k)}):
                if n < k + T: continue
                if plan(k, T) is None:
                    tot['noplan'] = tot.get('noplan', 0) + 1
                    fails.append(('noplan', k, T, n)); continue
                wmax = T - (k + 1) // 2
                if wmax < 0 or n - (3 * k + 1) // 2 < 0: continue
                for w in sorted({0, 1, wmax // 2, wmax}):
                    for kind in kinds:
                        for ev in (False, True):
                            for fill in ('random', 'early', 'late'):
                                W = rng.sample(range(n), w)
                                sig, od = make_adv(n, W, kind, rng)
                                res = run_window(n, k, T, W, sig, od, rng, ev, fill)
                                key = res if isinstance(res, str) else res[0]
                                tot[key] = tot.get(key, 0) + 1
                                if key != 'OK':
                                    fails.append((k, T, n, w, kind, ev, fill, key))
    print(tot)
    for f in fails[:30]:
        print(f)


if __name__ == '__main__':
    main()
