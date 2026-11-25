"""Finite-k Theorem W (CORE 47.2) for every residue of k.
Frame: kernel kappa of size h = floor(N - 3k/2) containing W and Z (|Z| = omega = N-k-T), six petal classes with the integer
plan of Lemma R (w = h).  Requests S_i = (kappa union P_i) minus Z, padded to exactly T points (so the rule never reads |S|).
Claim (FINITE_K.md 3.2): the frame exists iff 4T >= 3k and 4T != 3k+1, and then every window |W| <= T - ceil(k/2) is handled.
Test: the greedy rule (random order per class, random class table on S cap W) is applied verbatim to the real requests and
all pairs of the seven replies are checked.
Usage: py -3.14 thmW_frames.py [kmax]
"""
import sys, random, math, itertools


def plan_at(N, k, T, w):
    """integer classes (m1..m6) for kernel mass w (Lemma R), or None"""
    c = N - k
    M = N - w
    if w == N - 2 * T:
        q, r = divmod(T, 3)
        x, y, z = [q + (1 if i < r else 0) for i in range(3)]
        m = (x, x, y, y, z, z)
    elif w >= N - 2 * T + 1:
        q, r = divmod(M, 3)
        p = [q + (1 if i < r else 0) for i in range(3)]
        best = None
        for b in itertools.product((0, 1), repeat=3):
            hs = []
            for i in range(3):
                big, small = (p[i] + 1) // 2, p[i] // 2
                hs.append((big, small) if b[i] == 0 else (small, big))
            m = (hs[0][0], hs[0][1], hs[1][0], hs[1][1], hs[2][0], hs[2][1])
            mx = max(m[0] + m[2] + m[4], m[0] + m[3] + m[5], m[1] + m[2] + m[5], m[1] + m[3] + m[4])
            if best is None or mx < best[0]:
                best = (mx, m)
        m = best[1]
    else:
        return None
    m1, m2, m3, m4, m5, m6 = m
    if sum(m) != M or min(m) < 0:
        return None
    if any(w + a + b > c for a, b in ((m1, m2), (m3, m4), (m5, m6))):
        return None
    if max(m1 + m3 + m5, m1 + m4 + m6, m2 + m3 + m6, m2 + m4 + m5) > T:
        return None
    return m


def run_rule(k, T, N, wsize, rnd):
    c = N - k
    om = c - T
    h = (2 * N - 3 * k) // 2
    m = plan_at(N, k, T, h)
    assert m is not None
    pts = list(range(N))
    rnd.shuffle(pts)
    W = set(pts[:wsize])
    # class table on S cap W (hash of the frozenset), random order per class
    orders, table = {}, {}

    def sigma(S):
        key = frozenset(S & W)
        if key not in table:
            table[key] = rnd.randrange(8)
        return table[key]

    def order(r):
        if r not in orders:
            o = pts[:]
            rnd.shuffle(o)
            orders[r] = {v: i for i, v in enumerate(o)}
        return orders[r]

    def reply(S):
        r = sigma(S)
        o = order(r)
        free = sorted((v for v in pts if v not in S), key=lambda v: o[v])
        return set(S) | set(free[:c - len(S)])
    r0 = sigma(set(W))                       # class of any request containing W
    o0 = order(r0)
    Z = set(sorted((v for v in pts if v not in W), key=lambda v: o0[v])[:om])
    others = [v for v in pts if v not in W and v not in Z]
    rnd.shuffle(others)
    kappa = W | Z | set(others[:h - wsize - om])
    rest = others[h - wsize - om:]
    cls, pos = [], 0
    for mm in m:
        cls.append(set(rest[pos:pos + mm]))
        pos += mm
    assert pos == len(rest)
    Ks = []
    for (i, j) in ((0, 1), (2, 3), (4, 5)):
        L = kappa | cls[i] | cls[j]
        assert len(L) <= c
        S = L - Z
        pad = [v for v in pts if v not in L]
        rnd.shuffle(pad)
        need = T - len(S)
        assert 0 <= need <= len(pad)
        S |= set(pad[:need])
        assert len(S) == T and W <= S and not (S & Z)
        K = reply(S)
        assert K >= L, "pencil line not inside reply"
        Ks.append(K)
    for (i, j, l) in ((0, 2, 4), (0, 3, 5), (1, 2, 5), (1, 3, 4)):
        L = cls[i] | cls[j] | cls[l]
        assert len(L) <= T
        Ks.append(reply(L))
    cov = [0] * N
    for jj, K in enumerate(Ks):
        assert len(K) == c
        for v in K:
            cov[v] |= 1 << jj
    ms = set(cov)
    return 0 not in ms and all(a & b for a in ms for b in ms)


def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    rnd = random.Random(3)
    frames = noframe = runs = bad = 0
    noframe_list = []
    byres = {}
    for k in range(2, kmax + 1):
        for T in range(math.ceil(3 * k / 4), math.ceil(3 * k / 4) + 3):
            wmax = T - (k + 1) // 2
            for N in range(k + T, 3 * k + 3):
                h = (2 * N - 3 * k) // 2
                om = N - k - T
                if h < om:
                    continue
                m = plan_at(N, k, T, h)
                if m is None:
                    noframe += 1
                    noframe_list.append((k, T, N, 4 * T - 3 * k))
                    continue
                frames += 1
                for ws in sorted({0, wmax // 2, wmax}):
                    if ws < 0 or ws + om > h:
                        continue
                    for _ in range(2):
                        runs += 1
                        ok = run_rule(k, T, N, ws, rnd)
                        byres.setdefault(k % 4, [0, 0])[0] += 1
                        if not ok:
                            bad += 1
                            byres[k % 4][1] += 1
                            print("FAIL", k, T, N, ws)
    print(f"k<=%d: frames exist for {frames} (k,T,N); NO frame for {noframe}; rule runs {runs}, failures {bad}" % kmax)
    print("runs by k mod 4 (runs, failures):", byres)
    bad_defects = [x for x in noframe_list if x[3] != 1]
    print("no-frame cases with 4T-3k != 1:", len(bad_defects), bad_defects[:5])
    print("no-frame cases all have 4T = 3k+1:", all(x[3] == 1 for x in noframe_list), "; count", len(noframe_list))


main()
