"""Independent verifier for CORE.md Thm T (sec 3), Thm Q (sec 4) / Q' (sec 37), Thm P (sec 5), slack count (sec 2).
Written from the statements only.  Integer (finite-k) setting: |V| = N, co-edge size c = N-k, request size <= T,
k+T <= N.  A win = every pair {x,y} (x=y included) lies in a common reply K_i.

usage: py tqp_verify.py [T|Q|P|S|R|all] [seed]
"""
import itertools, random, sys, math
from functools import lru_cache


# ---------------------------------------------------------------- common
def wins(Ks, N):
    """Ks: list of sets of points 0..N-1. True iff the co-edges cover all pairs (incl. x=y)."""
    cov = [0] * N
    for j, K in enumerate(Ks):
        for x in K:
            cov[x] |= 1 << j
    if any(m == 0 for m in cov):
        return False
    ms = set(cov)
    for a in ms:
        for b in ms:
            if a & b == 0:
                return False
    return True


def uncovered_pairs(Ks, N):
    cov = [0] * N
    for j, K in enumerate(Ks):
        for x in K:
            cov[x] |= 1 << j
    n = 0
    for x in range(N):
        for y in range(x, N):
            if cov[x] & cov[y] == 0:
                n += 1
    return n


def answer(S, c, N, rnd, mode, prefer=None, forbid=()):
    """adversary reply: S plus (c-|S|) further points. prefer = ordered list of preferred points."""
    rest = [x for x in range(N) if x not in S]
    need = c - len(S)
    assert 0 <= need <= len(rest), (need, len(rest))
    if mode == 'rand':
        add = rnd.sample(rest, need)
    elif mode == 'pref':
        pr = [x for x in prefer if x in rest]
        others = [x for x in rest if x not in pr]
        rnd.shuffle(others)
        add = (pr + others)[:need]
    return set(S) | set(add)


def hill(Ks_fixed, Ss, c, N, rnd, iters=300):
    """adversary: choose supersets K_i of S_i (size c) to maximise #uncovered pairs; returns best (n_uncovered, Ks)."""
    cur = [answer(S, c, N, rnd, 'rand') for S in Ss]
    best = uncovered_pairs(Ks_fixed + cur, N)
    for it in range(iters):
        if best > 0:
            return best, cur
        i = rnd.randrange(len(Ss))
        K = cur[i]
        free_in = [x for x in K if x not in Ss[i]]
        free_out = [x for x in range(N) if x not in K]
        if not free_in or not free_out:
            continue
        x, y = rnd.choice(free_in), rnd.choice(free_out)
        K2 = (K - {x}) | {y}
        new = cur[:i] + [K2] + cur[i + 1:]
        sc = uncovered_pairs(Ks_fixed + new, N)
        if sc >= best:
            best, cur = sc, new
    return best, cur


# ---------------------------------------------------------------- Theorem T
def build_T(a, b, d, e1, e2, e3, g, kap, k, N):
    """cells -> point sets. returns (K1,K2,K3, cells dict) with |K_i| = c."""
    pts = iter(range(N))
    cell = {}
    for nm, n in (('a', a), ('b', b), ('d', d), ('e1', e1), ('e2', e2), ('e3', e3), ('g', g), ('kap', kap)):
        cell[nm] = [next(pts) for _ in range(n)]
    K1 = set(cell['a'] + cell['b'] + cell['e1'] + cell['kap'])
    K2 = set(cell['a'] + cell['d'] + cell['e2'] + cell['kap'])
    K3 = set(cell['b'] + cell['d'] + cell['e3'] + cell['kap'])
    return K1, K2, K3, cell


def T_instances(k, T, N):
    """all cell vectors (a,b,d,kap free; e_i, g forced) meeting the hypothesis of Thm T for some kappa split."""
    c = N - k
    out = []
    for kap in range(0, c + 1):
        for a in range(0, c + 1 - kap):
            for b in range(0, c + 1 - kap - a):
                for d in range(0, c + 1 - kap - a - b):
                    e1 = c - a - b - kap
                    e2 = c - a - d - kap
                    e3 = c - b - d - kap
                    if min(e1, e2, e3) < 0:
                        continue
                    g = N - (a + b + d + e1 + e2 + e3 + kap)
                    if g < 0:
                        continue
                    if e1 + e2 + e3 > T:
                        continue
                    s4, s5, s6 = T - (a + e3 + g), T - (b + e2 + g), T - (d + e1 + g)
                    if min(s4, s5, s6) < 0 or s4 + s5 + s6 < kap:
                        continue
                    out.append((a, b, d, e1, e2, e3, g, kap))
    return out


def run_T(seed=1, verbose=True):
    rnd = random.Random(seed)
    tot = bad = 0
    tight = 0
    for k in range(1, 9):
        for T in range(math.ceil(3 * k / 4) - 1, k + 3):     # includes T < 3k/4 (empty) and T > k
            for N in range(k + T, 3 * k + 3):
                if T < 1:
                    continue
                c = N - k
                for (a, b, d, e1, e2, e3, g, kap) in T_instances(k, T, N):
                    K1, K2, K3, cell = build_T(a, b, d, e1, e2, e3, g, kap, k, N)
                    assert len(K1) == len(K2) == len(K3) == c
                    # kappa split: greedy
                    s = [T - (a + e3 + g), T - (b + e2 + g), T - (d + e1 + g)]
                    kp = list(cell['kap'])
                    parts = []
                    for j in range(3):
                        take = min(s[j], len(kp))
                        parts.append(kp[:take])
                        kp = kp[take:]
                    assert not kp
                    S4 = set(cell['a'] + cell['e3'] + cell['g'] + parts[0])
                    S5 = set(cell['b'] + cell['e2'] + cell['g'] + parts[1])
                    S6 = set(cell['d'] + cell['e1'] + cell['g'] + parts[2])
                    S7 = set(cell['e1'] + cell['e2'] + cell['e3'])
                    Ss = [S4, S5, S6, S7]
                    assert all(len(S) <= T for S in Ss), "budget"
                    if (e1 + e2 + e3 == T) or min(s) == 0:
                        tight += 1
                    for rep in range(3):
                        n_unc, Ks = hill([K1, K2, K3], Ss, c, N, rnd, iters=60)
                        tot += 1
                        if n_unc:
                            bad += 1
                            print("T FAIL", k, T, N, (a, b, d, e1, e2, e3, g, kap))
    if verbose:
        print(f"T: {tot} plays, {bad} failures, {tight} boundary instances")
    return bad


def T_closed_form(seed=2):
    """kappa = 0 closed form of sec 3: a,b,d <= (T+N-2k)/2 and a+b+d >= (3N-3k-T)/2 <=> hypotheses (when e_i,g >= 0)."""
    bad = tot = 0
    for k in range(1, 13):
        for T in range(1, k + 4):
            for N in range(k + T, 3 * k + 3):
                c = N - k
                for a in range(c + 1):
                    for b in range(c + 1):
                        for d in range(c + 1):
                            e1, e2, e3 = c - a - b, c - a - d, c - b - d
                            g = N - (a + b + d + e1 + e2 + e3)
                            if min(e1, e2, e3, g) < 0:
                                continue
                            hyp = (a + e3 + g <= T and b + e2 + g <= T and d + e1 + g <= T and e1 + e2 + e3 <= T)
                            cf = (2 * max(a, b, d) <= T + N - 2 * k) and (2 * (a + b + d) >= 3 * N - 3 * k - T)
                            tot += 1
                            if hyp != cf:
                                bad += 1
                                if bad < 5:
                                    print("closed form mismatch", k, T, N, a, b, d)
    print(f"T closed form: {tot} cell vectors, {bad} mismatches")
    return bad


# ---------------------------------------------------------------- Theorem Q / Q'
MATCH = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
TYPES = [frozenset(s) for r in range(5) for s in itertools.combinations(range(4), r)]


def Q_instance(rnd, k, N, bias=None):
    c = N - k
    pair = {frozenset(p): rnd.randint(0, bias or c) for p in itertools.combinations(range(4), 2)}
    tri = {frozenset(p): rnd.randint(0, bias or c) for p in itertools.combinations(range(4), 3)}
    u4 = rnd.randint(0, bias or c)
    cnt = {frozenset(): 0}
    for p, v in pair.items():
        cnt[p] = v
    for p, v in tri.items():
        cnt[p] = v
    cnt[frozenset(range(4))] = u4
    for i in range(4):
        used = sum(v for I, v in cnt.items() if i in I and len(I) >= 2)
        s = c - used
        if s < 0:
            return None
        cnt[frozenset([i])] = s
    s0 = N - sum(cnt.values())
    if s0 < 0:
        return None
    cnt[frozenset()] = s0
    return cnt


def Q_check(cnt, k, T, N, rnd, verbose=False):
    """returns (applicable, ok). applicable = hypotheses of Q hold (with an integer tau-distribution)."""
    c = N - k
    s0, s1 = cnt[frozenset()], sum(cnt[frozenset([i])] for i in range(4))
    u3 = sum(cnt[I] for I in TYPES if len(I) == 3)
    u4 = cnt[frozenset(range(4))]
    p = sum(cnt[I] for I in TYPES if len(I) == 2)
    W = u3 + 2 * u4 + s1
    sigma = s0 + s1
    base = [cnt[frozenset(m[0])] + cnt[frozenset(m[1])] + s0 + s1 for m in MATCH]
    room = [T - b for b in base]
    # identities of sec 4 and 37
    assert sum(base) + u3 + u4 == 4 * k - N + W, "load identity"
    assert W == 2 * N - 4 * k + 2 * sigma, "Q' identity"
    condQ = all(r >= 0 for r in room) and sum(room) >= u3 + u4          # exists integer tau split
    condQ_W = all(r >= 0 for r in room) and (4 * k - N + W <= 3 * T)
    condQp = all(r >= 0 for r in room) and (N + 2 * sigma <= 3 * T)     # (3t-N)/2 >= sigma
    assert condQ == condQ_W == condQp, ("Q vs Q' disagree", cnt)
    if not condQ:
        return False, True
    # build points
    pts = iter(range(N))
    pset = {I: [next(pts) for _ in range(cnt[I])] for I in TYPES}
    Ks = [set(x for I in TYPES if i in I for x in pset[I]) for i in range(4)]
    assert all(len(K) == c for K in Ks)
    Ss = []
    heavy = [x for I in TYPES if len(I) >= 3 for x in pset[I]]
    rnd.shuffle(heavy)
    for r, m in enumerate(MATCH):
        S = set(pset[frozenset(m[0])] + pset[frozenset(m[1])] + pset[frozenset()] + [x for i in range(4) for x in pset[frozenset([i])]])
        take = room[r]
        S |= set(heavy[:take])
        heavy = heavy[take:]
        Ss.append(S)
    assert not heavy
    assert all(len(S) <= T for S in Ss)
    ok = True
    for rep in range(3):
        n_unc, _ = hill(Ks, Ss, c, N, rnd, iters=40)
        if n_unc:
            ok = False
            print("Q FAIL", k, T, N, {tuple(sorted(I)): v for I, v in cnt.items() if v})
    return True, ok


def run_Q(seed=1, samples=1500000):
    rnd = random.Random(seed)
    app = bad = tot = 0
    for _ in range(samples):
        k = rnd.randint(2, 9)
        T = rnd.randint(math.ceil(3 * k / 4) - 1, k + 2)
        if T < 1:
            continue
        N = rnd.randint(k + T, 3 * k + 2)
        cnt = Q_instance(rnd, k, N, bias=rnd.choice([None, 2, 3]))
        if cnt is None:
            continue
        tot += 1
        a, o = Q_check(cnt, k, T, N, rnd)
        app += a
        bad += (a and not o)
    print(f"Q: {tot} quadruples, {app} satisfy the hypotheses, {bad} failures (Q == Q' conditions asserted equal on all)")
    return bad


# ---------------------------------------------------------------- Theorem P
@lru_cache(maxsize=None)
def Mmax(P, T):
    """max total mass of six integer classes m1..m6 with pair sums (m1+m2, m3+m4, m5+m6) <= P and the four triples
    (135,146,236,245) <= T  (Fano plane with point o; lines through o = {o,1,2},{o,3,4},{o,5,6})."""
    best = -1
    for m1 in range(0, min(P, T) + 1):
        for m2 in range(0, min(P - m1, T) + 1):
            for m3 in range(0, min(T - m1, T - m2) + 1):
                for m4 in range(0, min(P - m3, T - m1, T - m2) + 1):
                    U5 = min(T - m1 - m3, T - m2 - m4)
                    U6 = min(T - m1 - m4, T - m2 - m3)
                    if U5 < 0 or U6 < 0:
                        continue
                    tot = m1 + m2 + m3 + m4 + min(P, U5 + U6)
                    if tot > best:
                        best = tot
    return best


def find_classes(M, P, T):
    for m1 in range(0, min(P, T) + 1):
        for m2 in range(0, min(P - m1, T) + 1):
            for m3 in range(0, min(T - m1, T - m2) + 1):
                for m4 in range(0, min(P - m3, T - m1, T - m2) + 1):
                    U5 = min(T - m1 - m3, T - m2 - m4)
                    U6 = min(T - m1 - m4, T - m2 - m3)
                    if U5 < 0 or U6 < 0:
                        continue
                    R = M - (m1 + m2 + m3 + m4)
                    if 0 <= R <= min(P, U5 + U6):
                        m5 = min(U5, R)
                        m6 = R - m5
                        if m6 <= U6 and m5 + m6 <= P:
                            return (m1, m2, m3, m4, m5, m6)
    return None


def P_wo_range(k, T, N, Z):
    lo = max(Z, N - 2 * T)
    hi = (2 * N - 3 * k) // 2          # floor(N - 3k/2)
    return lo, hi


def P_exists_integer_plan(k, T, N, Z):
    c = N - k
    lo, hi = P_wo_range(k, T, N, Z)
    for wo in range(max(lo, 0), hi + 1):
        M = N - wo
        P = c - wo
        if P < 0:
            continue
        if M <= Mmax(P, T):
            return wo
    return None


def run_P_rounding(kmax=16):
    """for every (k,T,N,|Z|) satisfying the hypotheses of P, is there an integer plan of the proof's shape?"""
    fails = []
    tot = 0
    for k in range(1, kmax + 1):
        for T in range(math.ceil(3 * k / 4), k + 4):
            for N in range(k + T, 3 * k + 3):
                c = N - k
                om = c - T
                for Z in range(om, (2 * N - 3 * k) // 2 + 1):
                    tot += 1
                    if P_exists_integer_plan(k, T, N, Z) is None:
                        fails.append((k, T, N, Z))
    print(f"P rounding: {tot} parameter sets, {len(fails)} with NO integer plan of the proof's shape")
    for f in fails[:40]:
        print("   (k,T,N,|Z|) =", f)
    return fails


def P_play(k, T, N, Z, rnd, wo):
    c = N - k
    om = c - T
    M, P = N - wo, c - wo
    m = find_classes(M, P, T)
    assert m is not None
    pts = list(range(N))
    zset = rnd.sample(pts, Z)
    Zs = set(zset)
    # V_o ⊇ Z of size wo
    others = [x for x in pts if x not in Zs]
    rnd.shuffle(others)
    Vo = set(zset) | set(others[:wo - Z])
    rest = others[wo - Z:]
    cls = []
    pos = 0
    for mm in m:
        cls.append(set(rest[pos:pos + mm]))
        pos += mm
    assert pos == len(rest)
    # lines through o: {o,1,2},{o,3,4},{o,5,6}; others 135,146,236,245  (classes indexed 1..6 -> cls[0..5])
    lines_o = [(0, 1), (2, 3), (4, 5)]
    lines_n = [(0, 2, 4), (0, 3, 5), (1, 2, 5), (1, 3, 4)]
    Ks, Ss = [], []
    pool_adv_modes = rnd.choice(['rand', 'allZ_first', 'Z_last'])

    def reply(S):
        rest_pts = [x for x in pts if x not in S]
        need = c - len(S)
        zfree = [x for x in rest_pts if x in Zs]
        if len(zfree) >= need:                       # pool rule binds: K\S ⊆ Z
            add = rnd.sample(zfree, need)
        else:                                        # free: adversary chooses (mode)
            if pool_adv_modes == 'Z_last':
                nz = [x for x in rest_pts if x not in Zs]
                rnd.shuffle(nz)
                add = (nz + zfree)[:need]
            else:
                add = rnd.sample(rest_pts, need)
        return set(S) | set(add)
    for (i, j) in lines_o:
        L = Vo | cls[i] | cls[j]
        assert len(L) <= c
        Zpp = set(rnd.sample(zset, om))
        S = L - Zpp
        assert len(S) <= T
        pad = [x for x in pts if x not in S and x not in Zpp]
        rnd.shuffle(pad)
        S = S | set(pad[:T - len(S)])
        assert len(S) == T and not (S & Zpp)
        Ss.append(S)
        Ks.append(reply(S))
        assert Ks[-1] >= L, "line through o not contained in reply"
    for (i, j, l) in lines_n:
        L = cls[i] | cls[j] | cls[l]
        assert len(L) <= T
        Ss.append(L)
        Ks.append(reply(L))
    assert all(len(K) == c for K in Ks)
    return wins(Ks, N)


def run_P(seed=1, plays=40):
    rnd = random.Random(seed)
    fails = run_P_rounding(14)
    failset = set(fails)
    tot = bad = 0
    params = []
    for k in range(2, 15):
        for T in range(math.ceil(3 * k / 4), k + 3):
            for N in range(k + T, 3 * k + 2):
                c = N - k
                om = c - T
                for Z in {om, (2 * N - 3 * k) // 2, (om + (2 * N - 3 * k) // 2) // 2}:
                    if om <= Z <= (2 * N - 3 * k) // 2 and (k, T, N, Z) not in failset:
                        params.append((k, T, N, Z))
    rnd.shuffle(params)
    for (k, T, N, Z) in params[:1500]:
        c = N - k
        lo, hi = P_wo_range(k, T, N, Z)
        for _ in range(plays // 10):
            wo = None
            cand = [w for w in range(max(lo, 0), hi + 1) if N - w <= Mmax(c - w, T) and c - w >= 0]
            wo = rnd.choice(cand)
            tot += 1
            if not P_play(k, T, N, Z, rnd, wo):
                bad += 1
                print("P FAIL", (k, T, N, Z, wo))
    print(f"P: {tot} plays on {min(len(params),1500)} parameter sets, {bad} failures")
    return bad


# ---------------------------------------------------------------- slack count (sec 2)
def run_S(seed=1, samples=20000):
    rnd = random.Random(seed)
    bad = n = 0
    cnt_win = 0
    for _ in range(samples):
        k = rnd.randint(2, 9)
        N = rnd.randint(k + 1, 2 * k - 1) if rnd.random() < 0.8 else rnd.randint(2 * k, 3 * k)
        c = N - k
        Ks = [set(rnd.sample(range(N), c)) for _ in range(7)]
        I = [[i for i in range(7) if x in Ks[i]] for x in range(N)]
        # 2.1 waste identity (always)
        assert sum(len(i) - 3 for i in I) == 4 * N - 7 * k
        if wins(Ks, N):
            cnt_win += 1
            if N < 2 * k:
                n += 1
                assert all(len(i) >= 3 for i in I), "co-type of size <3 in winning seven, N<2k"
    print(f"S 2.1: random sevens ok; {cnt_win} winning sevens seen (rest of 2.1/2.2 checked in run_S2)")
    return bad


FANO_LINES = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]


def run_S2(seed=3):
    """2.2: for every winning seven found (hill-climb search, N<2k) and every choice of 3-sets l(x) ⊆ I_x, and every
    request family S_i (|S_i| = T) inside K_i, sum |L_i \\ S_i| >= 3N - 7T, and at most 2 replies with L_i ⊄ S_i
    forces N <= 5T - 2k (contrapositive of the claim, also for non-full requests)."""
    rnd = random.Random(seed)
    checked = 0
    # build winning sevens as Fano blow-ups with padding
    for trial in range(200000):
        k = rnd.randint(4, 12)
        N = rnd.randint(math.ceil(7 * k / 4), 2 * k - 1)
        c = N - k
        # random class masses over 7 point-classes (pencil labelling, co-edges = lines) subject to line mass <= c
        m = [0] * 7
        for _ in range(N):
            m[rnd.randrange(7)] += 1
        pts = []
        for cl in range(7):
            pts += [cl] * m[cl]
        # co-edge for line L_i must contain classes on it
        lines = FANO_LINES
        base = [set(x for x, cl in enumerate(pts) if cl in lines[i]) for i in range(7)]
        if any(len(b) > c for b in base):
            continue
        Ks = []
        for b in base:
            extra = [x for x in range(N) if x not in b]
            Ks.append(b | set(rnd.sample(extra, c - len(b))))
        assert wins(Ks, N)
        I = [[i for i in range(7) if x in Ks[i]] for x in range(N)]
        for T in range(math.ceil(3 * k / 4), c + 1):
            for rep in range(2):
                Ss = [set(rnd.sample(sorted(K), min(T, len(K)))) for K in Ks]
                ell = [rnd.sample(i, 3) for i in I]
                L = [set(x for x in range(N) if i in ell[x]) for i in range(7)]
                assert sum(len(l) for l in L) == 3 * N
                assert all(L[i] <= Ks[i] for i in range(7))
                assert sum(len(L[i] - Ss[i]) for i in range(7)) >= 3 * N - 7 * T
                nonempty = sum(1 for i in range(7) if L[i] - Ss[i])
                if N > 5 * T - 2 * k:
                    assert nonempty >= 3, ("claim 2.2 violated", k, T, N)
                checked += 1
    print(f"S 2.2: {checked} (seven, lines, requests) triples checked")


if __name__ == "__main__":
    which = sys.argv[1] if len(sys.argv) > 1 else "all"
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    if which in ("S", "all"):
        run_S(seed)
        run_S2(seed)
    if which in ("T", "all"):
        T_closed_form(seed)
        run_T(seed)
    if which in ("Q", "all"):
        run_Q(seed)
    if which == "R":
        run_P_rounding(int(sys.argv[2]) if len(sys.argv) > 2 else 16)
    if which in ("P", "all"):
        run_P(seed)
