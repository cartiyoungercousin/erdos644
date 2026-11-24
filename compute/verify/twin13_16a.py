r"""Independent verification of TWIN.md s13 (anchor reduction + padding transfer) and s16.3 (Prop 16.A).
Run:  py twin13_16a.py
Own definitions: game = requester asks S (|S|<=T), adversary must answer an edge (k-set) disjoint from S;
requester wins if the 7 replies have no 2-point transversal (pair x,y, x=y allowed).
"""
import itertools, random, sys, math


def cov_pairs(E, pts):
    pts = list(pts)
    for x in pts:
        for y in pts:
            if all((x in e) or (y in e) for e in E):
                return True
    return False


# ------------------------------------------------ part 1: Lemma 13.1 / Theorem A (i)
def part1(trials=20000, seed=1):
    rnd = random.Random(seed)
    cnt = 0
    while cnt < trials:
        n = rnd.randint(6, 12)
        k = rnd.randint(2, 5)
        E = [frozenset(rnd.sample(range(n), k)) for _ in range(7)]
        if E[0] & E[1] & E[2]:
            continue
        cnt += 1
        V = E[0] | E[1] | E[2]
        full = cov_pairs(E, range(n))
        assert full == cov_pairs(E, V)
        tr = [e & V for e in E]
        assert full == cov_pairs(tr, V)
        j = rnd.randrange(3, 7)
        big = list(tr)
        big[j] = tr[j] | frozenset(rnd.sample(sorted(V), rnd.randint(0, len(V))))
        if full:
            assert cov_pairs(big, V)
    return cnt


# ------------------------------------------------ Theorem C strategy with integer splitting (ILP min-max load)
def balanced_requests(anchors, T=None):
    a = [frozenset(x) for x in anchors]
    assert not (a[0] & a[1] & a[2])
    P = {}
    for (i, j) in ((0, 1), (0, 2), (1, 2)):
        P[(i, j)] = sorted(a[i] & a[j])
    inP = set(x for v in P.values() for x in v)
    Q = {c: sorted(a[c] - inP) for c in range(3)}
    M = {(0, 1): [(4, 7), (5, 6)], (0, 2): [(4, 6), (5, 7)], (1, 2): [(4, 5), (6, 7)]}
    allp = list(itertools.combinations([4, 5, 6, 7], 2))
    opp = {2: (0, 1), 1: (0, 2), 0: (1, 2)}
    QT = {c: [t for t in allp if t not in M[opp[c]]] for c in range(3)}
    # exact min-max load by DFS over integer splits (no external solver)
    plist = [(P[ab], M[ab]) for ab in P] + [(Q[c], QT[c]) for c in Q]
    def comps(total, parts):
        if parts == 1:
            yield (total,)
            return
        for i in range(total + 1):
            for r in comps(total - i, parts - 1):
                yield (i,) + r
    opts = []
    for pts, types in plist:
        lst = []
        for c in comps(len(pts), len(types)):
            ld = [0, 0, 0, 0]
            for cc, t in zip(c, types):
                for rd in t:
                    ld[rd - 4] += cc
            lst.append((tuple(ld), c))
        # dedupe by load vector
        d = {}
        for ld, c in lst:
            d.setdefault(ld, c)
        opts.append(list(d.items()))
    best = [10**9, None]
    def dfs(i, cur, choice):
        if max(cur) >= best[0]:
            return
        if i == len(opts):
            best[0] = max(cur); best[1] = list(choice); return
        for ld, c in opts[i]:
            dfs(i + 1, tuple(x + y for x, y in zip(cur, ld)), choice + [c])
    dfs(0, (0, 0, 0, 0), [])
    var = {}
    for (pts, types), c in zip(plist, best[1]):
        pass
    parts = [(None, pts, types) for pts, types in plist]
    counts = best[1]
    req = {rd: set() for rd in (4, 5, 6, 7)}
    for (name, pts, types), cs in zip(parts, counts):
        pos = 0
        for t, c in zip(types, cs):
            for x in pts[pos:pos + c]:
                for rd in t:
                    req[rd].add(x)
            pos += c
    return max(len(req[r]) for r in req), [req[r] for r in (4, 5, 6, 7)]


# ------------------------------------------------ part 2: padding transfer
def part2(seed=2, samples=30000):
    rnd = random.Random(seed)
    k, T = 4, 3
    anchors = [{0, 1, 2, 3}, {0, 1, 4, 5}, {2, 3, 4, 5}]
    ml, req = balanced_requests(anchors)
    assert ml <= T, ml
    V = set(range(6))
    res = {}
    for extra in (2, 4, 6):
        n = 6 + extra
        G = list(range(n))
        opts = []
        for r in req:
            free = [x for x in G if x not in r]
            opts.append([frozenset(c) for c in itertools.combinations(free, k)])
        total = math.prod(len(o) for o in opts)
        if total <= samples:
            it = itertools.product(*opts)
        else:
            it = (tuple(rnd.choice(o) for o in opts) for _ in range(samples))
        m = 0
        for later in it:
            m += 1
            E = [frozenset(x) for x in anchors] + list(later)
            assert not cov_pairs(E, G), later
            tr = [e & V for e in E]
            assert not cov_pairs(tr, V)
        res[extra] = (m, total <= samples)
    return res


def part2b(trials=3000, seed=3):
    """Random adaptive confined strategies (arbitrary function of padded history): padded uncoverable => real uncoverable.
    Also: the real reply may have |trace| < min(k,|V\\S|); padding is arbitrary inside V\\S."""
    rnd = random.Random(seed)
    cnt = 0
    for _ in range(trials):
        k = rnd.randint(3, 5)
        T = rnd.randint(k // 2 + 1, k + 1)
        n_out = rnd.randint(0, 4)
        # anchors with empty triple intersection
        while True:
            nV = rnd.randint(k + 1, 3 * k)
            A = [frozenset(rnd.sample(range(nV), k)) for _ in range(3)]
            if not (A[0] & A[1] & A[2]):
                break
        V = A[0] | A[1] | A[2]
        G = list(range(max(V) + 1 + n_out))
        Vl = sorted(V)
        E = list(A)
        Ep = list(A)
        for rd in range(4):
            S = set(rnd.sample(Vl, min(T, len(Vl))))
            freeG = [x for x in G if x not in S]
            if len(freeG) < k:
                break
            e = frozenset(rnd.sample(freeG, k))
            tr = e & V
            freeV = [x for x in Vl if x not in S]
            tgt = min(k, len(freeV))
            assert len(tr) <= tgt
            padp = list(tr) + rnd.sample([x for x in freeV if x not in tr], tgt - len(tr))
            E.append(e)
            Ep.append(frozenset(padp))
        if len(E) == 7:
            cnt += 1
            if not cov_pairs(Ep, V):
                assert not cov_pairs(E, G)
    return cnt


# ------------------------------------------------ part 3: Prop 16.A exact
def prop16A(k, T, n, rnd, cap=None):
    V = list(range(n))
    B1 = frozenset(range(k))
    alpha = max(0, n - 2 * T)
    a0 = frozenset(range(k, k + alpha))
    assert n - k >= alpha
    need = T - alpha
    assert 0 <= need <= k
    S2 = a0 | frozenset(rnd.sample(sorted(B1), need))
    assert len(S2) <= T
    free2 = [x for x in V if x not in S2]
    worst = 0
    fails = []
    cnt = 0
    nfail = 0
    cache = {}
    for B2 in itertools.combinations(free2, k):
        B2 = frozenset(B2)
        I = B1 & B2
        S3 = a0 | I
        if len(S3) > T:
            nfail += 1
            fails.append(('S3 too big', len(S3), T))
            continue
        free3 = [x for x in V if x not in S3]
        for B3 in itertools.combinations(free3, k):
            B3 = frozenset(B3)
            cnt += 1
            assert not (B1 & B2 & B3)
            U = B1 | B2 | B3
            assert not (U & a0) and len(U) <= 2 * T
            key = tuple(sorted((len(B1 & B2), len(B1 & B3), len(B2 & B3), len(B1 - B2 - B3), len(B2 - B1 - B3), len(B3 - B1 - B2))))
            sh = (len(B1 & B2), len(B1 & B3), len(B2 & B3), len(B1 - B2 - B3), len(B2 - B1 - B3), len(B3 - B1 - B2))
            if sh not in cache:
                cache[sh] = balanced_requests([B1, B2, B3])[0]
            ml = cache[sh]
            worst = max(worst, ml - T)
            if ml > T:
                nfail += 1
                if len(fails) < 3:
                    fails.append(('C-load', ml, T, len(U), sh))
    return cnt, 'max(load-T)=%d' % worst, nfail, fails[:3]


def shapes_C(maxU=12):
    """Exact finite threshold of Theorem C: for each |U|, worst shape min-max load vs ceil(|U|/2)."""
    out = {}
    for U in range(2, maxU + 1):
        w = 0
        arg = None
        for sizes in itertools.product(range(U + 1), repeat=6):
            if sum(sizes) != U:
                continue
            pts = iter(range(1000))
            A12, A13, A23, Q1, Q2, Q3 = [[next(pts) for _ in range(s)] for s in sizes]
            a = [set(A12 + A13 + Q1), set(A12 + A23 + Q2), set(A13 + A23 + Q3)]
            if any(len(x) == 0 for x in a):
                pass
            ml, _ = balanced_requests(a)
            if ml > w:
                w, arg = ml, sizes
        out[U] = (w, math.ceil(U / 2), arg)
    return out


if __name__ == '__main__':
    print('part1 lemma / Thm A(i) / monotone, random tuples:', part1())
    print('part2 padding transfer k=4,T=3 (exhaustive where possible):', part2())
    print('part2b random adaptive confined plays, real-vs-padded:', part2b())
    rnd = random.Random(7)
    for (k, T, n) in [(4, 3, 7), (4, 3, 6), (4, 4, 8), (4, 4, 9), (4, 4, 10), (5, 4, 9), (6, 5, 11), (6, 5, 12), (6, 4, 10), (6, 5, 13)]:
        ok = (n <= 3 * T - k / 2) and (n >= k + T)
        print('k,T,n=', (k, T, n), 'IN 16.A range' if ok else 'out of range', prop16A(k, T, n, rnd))
        sys.stdout.flush()
    print('Theorem C finite threshold (|U|: worst minmax load, ceil(|U|/2), shape):')
    for U, v in shapes_C(10).items():
        print(' ', U, v)
