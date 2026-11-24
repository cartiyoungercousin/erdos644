"""Independent verification of CORE 37 (Qprime), 38 (Sigma reduction), 39.2 (density form of Thm S).
Everything in point counts: k points per unit mass, T=request cap, n=|V|, c=n-k.  Exact integer arithmetic."""
import random, itertools, sys
from fractions import Fraction as F


def covers_all_pairs(sets, V):
    for x in V:
        for y in V:
            if x > y:
                continue
            if not any(x in s and y in s for s in sets):
                return False
    return True


# ---------------------------------------------------------------- A. Qprime
def q_instance(n, k, T, rng, iters=4000):
    c = n - k
    pool = [(0, 1), (2, 3), (0, 2), (1, 3), (0, 3), (1, 2), (0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3),
            (0, 1, 2, 3), (0,), (1,), (2,), (3,), ()]
    wts = [8, 8, 8, 8, 8, 8, 3, 3, 3, 3, 2, 1, 1, 1, 1, 1]
    typ = [rng.choices(pool, wts)[0] for _ in range(n)]

    def cost(typ):
        sz = [sum(1 for t in typ if i in t) for i in range(4)]
        return sum((s - c) ** 2 for s in sz)

    cur = cost(typ)
    for _ in range(iters):
        if cur == 0:
            break
        j = rng.randrange(n)
        old = typ[j]
        typ[j] = rng.choices(pool, wts)[0]
        new = cost(typ)
        if new <= cur:
            cur = new
        else:
            typ[j] = old
    return typ if cur == 0 else None


MATCH = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]


def qprime_test(n, k, T, rng):
    typ = q_instance(n, k, T, rng)
    if typ is None:
        return None
    V = list(range(n))
    K = [{x for x in V if i in typ[x]} for i in range(4)]
    cnt = lambda pred: sum(1 for t in typ if pred(len(t)))
    s0 = cnt(lambda m: m == 0); s1 = cnt(lambda m: m == 1); p = cnt(lambda m: m == 2)
    u3 = cnt(lambda m: m == 3); u4 = cnt(lambda m: m == 4)
    sig = s0 + s1
    W = u3 + 2 * u4 + s1
    assert W == 2 * n - 4 * k + 2 * sig, "W identity"
    cm = [sum(1 for t in typ if t in (a, b)) for a, b in MATCH]
    hyp = 2 * sig <= 3 * T - n and all(cm[r] + sig <= T for r in range(3))
    sl = [T - cm[r] - sig for r in range(3)]
    if all(s >= 0 for s in sl):
        tau_exists = sum(sl) >= u3 + u4
        assert tau_exists == (2 * sig <= 3 * T - n), "tau-iff"
    ok = None
    if hyp:
        S = [set() for _ in range(3)]
        for x in V:
            t = typ[x]
            if len(t) <= 1:
                for r in range(3):
                    S[r].add(x)
            elif len(t) == 2:
                for r, (a, b) in enumerate(MATCH):
                    if t in (a, b):
                        S[r].add(x)
        rest = [x for x in V if len(typ[x]) >= 3]
        r = 0
        for x in rest:
            while len(S[r]) >= T:
                r += 1
            S[r].add(x)
        ok = all(len(s) <= T for s in S) and covers_all_pairs(K + S, V)
    return hyp, ok


def pool_min_sigma(k, T):
    G = range(k + T)
    edges = [frozenset(e) for e in itertools.combinations(G, k)]
    best = 10 ** 9
    for q in itertools.combinations_with_replacement(range(len(edges)), 4):
        cntp = [0] * (k + T)
        for i in q:
            for x in edges[i]:
                cntp[x] += 1
        sig = sum(1 for v in cntp if v >= 3)
        best = min(best, sig)
    return best


# ---------------------------------------------------------------- B. (b) pencil, general form
def halves_ok(q, T):
    for x1 in range(q[0] + 1):
        for x2 in range(q[1] + 1):
            for x3 in range(q[2] + 1):
                y1, y2, y3 = q[0] - x1, q[1] - x2, q[2] - x3
                if max(x1 + x2 + x3, x1 + y2 + y3, y1 + x2 + y3, y1 + y2 + x3) <= T:
                    return (x1, x2, x3)
    return None


def test_b(n, k, T, rng, trials=300):
    c = n - k
    V = list(range(n))
    res = dict(tried=0, hyp=0, fail=0, failparity=[], upper_viol=0)
    for _ in range(trials):
        while True:
            K = [set(rng.sample(V, c)) for _ in range(3)]
            if K[0] | K[1] | K[2] == set(V):
                break
        kern = K[0] & K[1] & K[2]
        res['tried'] += 1
        if 2 * len(kern) > 3 * c - n:
            res['upper_viol'] += 1  # triple intersection > (3c-n)/2 impossible when union=V
        if len(kern) < n - 2 * T:
            continue
        res['hyp'] += 1
        rest = [x for x in V if x not in kern]
        Q = [[], [], []]
        for x in rest:
            Q[rng.choice([i for i in range(3) if x in K[i]])].append(x)
        sizes = tuple(len(q) for q in Q)
        xs = halves_ok(sizes, T)
        if xs is None:
            res['failparity'].append((sizes, len(kern)))
            continue
        A = [Q[i][:xs[i]] for i in range(3)]
        B = [Q[i][xs[i]:] for i in range(3)]
        S4 = set(A[0]) | set(A[1]) | set(A[2])
        S5 = set(A[0]) | set(B[1]) | set(B[2])
        S6 = set(B[0]) | set(A[1]) | set(B[2])
        S7 = set(B[0]) | set(B[1]) | set(A[2])
        assert max(len(s) for s in (S4, S5, S6, S7)) <= T
        if not covers_all_pairs(K + [S4, S5, S6, S7], V):
            res['fail'] += 1
    return res


# ---------------------------------------------------------------- C. Theorem T (c)
def test_c(n, k, T, rng, trials=400):
    c = n - k
    V = list(range(n))
    out = dict(hyp=0, fail=0, tried=0)
    for _ in range(trials):
        K = [set(rng.sample(V, c)) for _ in range(3)]
        K1, K2, K3 = K
        a = (K1 & K2) - K3; b = (K1 & K3) - K2; d = (K2 & K3) - K1
        e1 = K1 - K2 - K3; e2 = K2 - K1 - K3; e3 = K3 - K1 - K2
        g = set(V) - K1 - K2 - K3; ka = K1 & K2 & K3
        out['tried'] += 1
        kl = sorted(ka)
        found = None
        L = len(kl)
        for s4 in range(L + 1):
            for s5 in range(L - s4 + 1):
                s6 = L - s4 - s5
                if (len(a) + len(e3) + len(g) + s4 <= T and len(b) + len(e2) + len(g) + s5 <= T and
                        len(d) + len(e1) + len(g) + s6 <= T and len(e1) + len(e2) + len(e3) <= T):
                    found = (s4, s5, s6)
                    break
            if found:
                break
        if not found:
            continue
        out['hyp'] += 1
        s4, s5, s6 = found
        S4 = a | e3 | g | set(kl[:s4]); S5 = b | e2 | g | set(kl[s4:s4 + s5]); S6 = d | e1 | g | set(kl[s4 + s5:])
        S7 = e1 | e2 | e3
        if not covers_all_pairs(K + [S4, S5, S6, S7], V):
            out['fail'] += 1
    return out


# ---------------------------------------------------------------- D. density form
def density_test(vs, pi, T):
    cells = []
    off = 0
    for v in vs:
        cells.append(list(range(off, off + v)))
        off += v
    n = off
    cls = [frozenset(sum((list(s) for s in sel), [])) for sel in
           itertools.product(*[itertools.combinations(cells[j], pi[j]) for j in range(len(vs))])]
    idx = {K: i for i, K in enumerate(cls)}
    kap = [(3 * pi[j] - vs[j]) for j in range(len(vs))]
    assert all(x >= 0 and x % 2 == 0 for x in kap)
    kj = [x // 2 for x in kap]
    pj = [(vs[j] - pi[j]) // 2 for j in range(len(vs))]
    triples = set()

    def parts(items, sz):
        for A in itertools.combinations(items, sz):
            r = [x for x in items if x not in A]
            for B in itertools.combinations(r, sz):
                C = tuple(x for x in r if x not in B)
                yield A, B, C

    for kerch in itertools.product(*[itertools.combinations(cells[j], kj[j]) for j in range(len(vs))]):
        kern = set(sum((list(x) for x in kerch), []))
        remcells = [[x for x in cells[j] if x not in kern] for j in range(len(vs))]
        for ps in itertools.product(*[list(parts(remcells[j], pj[j])) for j in range(len(vs))]):
            mem = []
            for i in range(3):
                mem.append(frozenset(kern | set(sum((list(ps[j][i]) for j in range(len(vs))), []))))
            assert all(M in idx for M in mem)
            triples.add(frozenset(idx[M] for M in mem))
    deg = [0] * len(cls)
    for tr in triples:
        for v in tr:
            deg[v] += 1
    regular = len(set(deg)) == 1 and deg[0] > 0
    import highspy
    h = highspy.Highs(); h.setOptionValue("output_flag", False); h.setOptionValue("time_limit", 200.0)
    inf = highspy.kHighsInf
    for i in range(len(cls)):
        h.addVar(0, 1)
    h.changeColsIntegrality(len(cls), list(range(len(cls))), [highspy.HighsVarType.kInteger] * len(cls))
    h.changeColsCost(len(cls), list(range(len(cls))), [-1.0] * len(cls))
    for tr in triples:
        idxs = sorted(tr)
        h.addRow(-inf, 2, 3, idxs, [1.0, 1.0, 1.0])
    h.run()
    best = int(round(-h.getInfo().objective_function_value))
    avoid = max(sum(1 for K in cls if p not in K) for p in range(n))
    return len(cls), len(triples), regular, best, F(best, len(cls)), F(avoid, len(cls))


if __name__ == "__main__":
    rng = random.Random(1)
    which = sys.argv[1:] or ["A", "P", "B", "C", "D"]
    if "A" in which:
        for (n, k, T) in [(15, 8, 6), (15, 8, 7), (14, 8, 6), (13, 8, 6), (17, 8, 7), (11, 6, 5), (12, 6, 5),
                          (21, 12, 9), (22, 12, 10)]:
            tot = hyp = bad = 0
            for _ in range(600):
                r = qprime_test(n, k, T, rng)
                if r is None:
                    continue
                tot += 1
                if r[0]:
                    hyp += 1
                    if not r[1]:
                        bad += 1
            print("Q'", (n, k, T), "instances", tot, "hyp holds", hyp, "construction fails", bad)
    if "P" in which:
        for (k, T) in [(4, 3), (4, 2), (5, 4), (5, 3)]:
            print("pool k,T", k, T, "min sigma", pool_min_sigma(k, T), "bound k-T", k - T)
    if "B" in which:
        for (n, k, T) in [(15, 8, 6), (14, 8, 6), (15, 8, 7), (17, 8, 7), (11, 6, 5), (13, 6, 5), (21, 12, 9),
                          (23, 12, 10)]:
            r = test_b(n, k, T, rng, 600)
            print("(b)", (n, k, T), {x: (r[x] if x != 'failparity' else (len(r[x]), r[x][:3])) for x in r})
    if "C" in which:
        for (n, k, T) in [(15, 8, 6), (15, 8, 7), (14, 8, 6), (17, 8, 7), (21, 12, 9), (13, 8, 6), (12, 8, 6)]:
            print("(c)", (n, k, T), test_c(n, k, T, rng, 2000))
    if "D" in which:
        print("density", density_test([4, 3], [2, 1], 3))
        print("density", density_test([6, 5], [3, 2], 5))
