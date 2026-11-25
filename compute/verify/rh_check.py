# Independent verification of Theorem R (CORE 57.2) and Theorem H (58.1). Not reusing compute/core9.
import itertools, math, random, sys
import numpy as np
from math import comb, lgamma, log
from collections import Counter

def frames_local(g, q, half):
    """all perfect sunflowers on [g]: 3 q-sets, common pairwise intersection (q-half), union [g]. (F,3) bitmasks."""
    kn = q - half
    out = []
    pts = list(range(g))
    for ker in itertools.combinations(pts, kn):
        km = sum(1 << i for i in ker)
        rest = [p for p in pts if not (km >> p) & 1]
        first = rest[0]
        rm = sum(1 << p for p in rest)
        for a in itertools.combinations(rest[1:], half - 1):
            A = (1 << first) | sum(1 << i for i in a)
            r2 = [p for p in rest if not (A >> p) & 1]
            f2 = r2[0]
            for b in itertools.combinations(r2[1:], half - 1):
                B = (1 << f2) | sum(1 << i for i in b)
                C = rm ^ A ^ B
                out.append((km | A, km | B, km | C))
    return np.array(out, dtype=np.int64)

def Fform(k, T): return comb(k+T, T)*comb(T, k//2)*comb(k, k//2)//6
def Dform(k, T): return comb(T, k//2)*comb(k, k//2)//2

def h(x): return -x*log(x)-(1-x)*log(1-x)
def Phi(t): return (1+t)*h(t/(1+t)) + t*h(1/(2*t)) + log(2)

def part_A():
    print("== A. counting ==")
    for (k, T) in [(4, 3), (4, 4), (8, 6)]:
        fr = frames_local(k+T, T, k//2)
        F = Fform(k, T); D = Dform(k, T)
        assert len(fr) == F, (len(fr), F)
        assert len(set(map(tuple, np.sort(fr, 1).tolist()))) == F
        cnt = {}
        for i, f in enumerate(fr.tolist()):
            for s in f: cnt.setdefault(s, []).append(i)
        assert all(len(v) == D for v in cnt.values()) and len(cnt) == comb(k+T, T)
        keys = set()
        for f in fr.tolist():
            a, b, c = sorted(f)
            keys.update([(a, b), (a, c), (b, c)])
        assert len(keys) == 3*F   # no two distinct frames share two requests
        print((k, T), "F=", F, "D=", D, "no two frames share 2 requests; ordered sharing pairs F*3*(D-1)=", F*3*(D-1),
              "3D/F=%.3g 9/C=%.3g" % (3*D/F, 9/comb(k+T, T)))
    for t in [0.75, 0.76, 0.8, 5/6]:
        print("t=%.4f Phi=%.4f Phi/2=%.4f" % (t, Phi(t), Phi(t)/2))
    for k, T in [(8, 6), (40, 30), (100, 76), (400, 304), (4000, 3040)]:
        lf = (lgamma(k+T+1)-lgamma(T+1)-lgamma(k+1)) + (lgamma(T+1)-lgamma(k//2+1)-lgamma(T-k//2+1)) + (lgamma(k+1)-2*lgamma(k//2+1)) - log(6)
        print("k=%d T=%d rho=lnF/(2k)=%.4f" % (k, T, lf/2/k))
    for N, t in [(1.8, .76), (2.1, .76), (2.24, .76)]:
        print("requests exponent N=%.2f t=%.2f: %.3f nats/k" % (N, t, N*h(t/N)))

def poly6(nreq, R, rng):
    """degree-5 polynomial over GF(2^14) (6-wise independent), low log2(R) bits (uniform marginals)."""
    poly = (1 << 14) | (1 << 10) | (1 << 6) | 2 | 1  # x^14+x^10+x^6+x+1
    # check irreducible-ish: verify field by multiplicative order test of x via brute force on small sample
    def mul(a, b):
        r = 0
        while b:
            if b & 1: r ^= a
            b >>= 1; a <<= 1
            if a >> 14: a ^= poly
        return r
    co = [rng.randrange(1 << 14) for _ in range(6)]
    out = np.zeros(nreq, dtype=np.int64)
    for x in range(nreq):
        pt = x+1; acc = 0
        for c in reversed(co): acc = mul(acc, pt) ^ c
        out[x] = acc & (R-1)
    return out

def run_R(k, T, n, R, trials, heads_mode, sel_mode, rng):
    om = n-k-T
    F = Fform(k, T)
    fr = frames_local(k+T, T, k//2)
    V = list(range(n))
    reqs = np.array(sorted(sum(1 << i for i in c) for c in itertools.combinations(V, T)), dtype=np.int64)
    def pick_heads():
        if heads_mode == 'equal':
            B = rng.sample(V, om); return [B]*R
        if heads_mode == 'overlap':
            core = rng.sample(V, om); hs = []
            for _ in range(R):
                B = set(core); B.discard(rng.choice(core))
                while len(B) < om: B.add(rng.choice(V))
                hs.append(sorted(B))
            return hs
        return [rng.sample(V, om) for _ in range(R)]
    cache = {}
    glen = k+T
    def ids_for(B):
        key = tuple(sorted(B))
        if key in cache: return cache[key]
        G = [p for p in V if p not in B]
        gm = np.zeros_like(fr)
        for i, g in enumerate(G): gm |= ((fr >> i) & 1) << g
        ids = np.searchsorted(reqs, gm)
        assert (reqs[ids] == gm).all()
        if len(cache) < 600: cache[key] = ids
        return ids
    Xs = []
    for t in range(trials):
        heads = pick_heads()
        if sel_mode == 'indep': sig = np.array([rng.randrange(R) for _ in range(len(reqs))])
        else: sig = poly6(len(reqs), R, rng)
        X = 0
        for r in range(R):
            X += int((sig[ids_for(heads[r])] == r).all(axis=1).sum())
        Xs.append(X)
    return np.array(Xs), F

def part_B():
    print("== B. Theorem R Monte Carlo (8,6,16): moments ==")
    rng = random.Random(12345)
    for (k, T, n, R, trials, hm, sm) in [(8, 6, 16, 16, 40, 'rand', 'indep'), (8, 6, 16, 16, 40, 'equal', 'indep'),
                                         (8, 6, 16, 64, 40, 'rand', 'indep'),
                                         (8, 6, 16, 256, 30, 'rand', 'indep'), (8, 6, 16, 1024, 8, "rand", "indep"),
                                         (8, 6, 16, 16, 30, 'rand', 'hash6'), (8, 6, 16, 256, 20, 'rand', 'hash6')]:
        Xs, F = run_R(k, T, n, R, trials, hm, sm, rng)
        D = Dform(k, T)
        EX = F/R**2
        varb = EX + 3*F*D/R**4
        print("(%d,%d,%d) R=%d heads=%s sel=%s trials=%d: mean X=%.1f (F/R^2=%.1f) var=%.1f (bound %.1f) min X=%d  bound P(X=0)<=%.3g"
              % (k, T, n, R, hm, sm, trials, Xs.mean(), EX, Xs.var(ddof=1), varb, Xs.min(), R**2/F+9/comb(k+T, T)), flush=True)

def part_B2():
    print("== B2. small instances: empirical P(X=0) vs bound ==")
    rng = random.Random(7)
    for (k, T, n) in [(4, 3, 8), (4, 3, 9), (4, 4, 9), (4, 3, 10)]:
        om = n-k-T
        F = Fform(k, T)
        fr = frames_local(k+T, T, k//2)
        V = list(range(n))
        reqs = np.array(sorted(sum(1 << i for i in c) for c in itertools.combinations(V, T)), dtype=np.int64)
        cache = {}
        def ids_for(B):
            key = tuple(sorted(B))
            if key not in cache:
                G = [p for p in V if p not in B]
                gm = np.zeros_like(fr)
                for i, g in enumerate(G): gm |= ((fr >> i) & 1) << g
                cache[key] = np.searchsorted(reqs, gm)
            return cache[key]
        for R in [2, 3, 4, 6, 8, 12]:
            for hm in ['rand', 'equal']:
                zero = 0; N = 2000
                for _ in range(N):
                    heads = [rng.sample(V, om) for _ in range(R)] if hm == 'rand' else [rng.sample(V, om)]*R
                    sig = np.array([rng.randrange(R) for _ in range(len(reqs))])
                    X = 0
                    for r in range(R):
                        X += int((sig[ids_for(heads[r])] == r).all(axis=1).sum())
                        if X: break
                    zero += (X == 0)
                bound = R**2/F + 9/comb(k+T, T)
                flag = "VIOLATION" if (zero/N > bound + 4*math.sqrt(0.25/N)) else ""
                print((k, T, n), "R=%d heads=%s P(X=0)=%.4f bound=%.4f %s" % (R, hm, zero/N, bound, flag), flush=True)

def part_H():
    print("== H. kernel density: max pencil-free member set over one kernel ==")
    import scipy.optimize as so
    from scipy.sparse import lil_matrix
    for k in [4, 8]:
        g = 3*k//2; hh = k//2
        halves = [sum(1 << i for i in c) for c in itertools.combinations(range(g), hh)]
        hid = {m: i for i, m in enumerate(halves)}
        full = (1 << g)-1
        parts = []
        for A in halves:
            if not A & 1: continue
            rest = [i for i in range(g) if not (A >> i) & 1]
            for b in itertools.combinations(rest[1:], hh-1):
                B = (1 << rest[0]) | sum(1 << i for i in b)
                parts.append((hid[A], hid[B], hid[full ^ A ^ B]))
        cnt = [0]*len(halves)
        for p in parts:
            for x in p: cnt[x] += 1
        d = comb(k, hh)//2
        assert all(c == d for c in cnt) and len(parts) == len(halves)*d//3
        A = lil_matrix((len(parts), len(halves)))
        for j, p in enumerate(parts):
            for x in p: A[j, x] = 1
        res = so.milp(c=-np.ones(len(halves)), constraints=so.LinearConstraint(A.tocsr(), -np.inf, 2),
                      integrality=np.ones(len(halves)), bounds=so.Bounds(0, 1))
        mx = round(-res.fun)
        kl = comb(g-1, hh)
        print("k=%d halves=%d partitions=%d  MILP max pencil-free=%d  Kleitman=%d  2/3*halves=%.2f" % (k, len(halves), len(parts), mx, kl, 2*len(halves)/3))
        assert mx == kl == 2*len(halves)//3
        Ks = {m for m in halves if not m & 1}
        assert len(Ks) == kl
        print("   Kleitman extremal set pencil-free:", all(not all(halves[x] in Ks for x in p) for p in parts))
        ok = True
        for m in halves:
            if m in Ks: continue
            S2 = Ks | {m}
            if not any(all(halves[x] in S2 for x in p) for p in parts): ok = False
        print("   every extra half creates a pencil:", ok)

def finish_55_2(k, n, T, kappa, P, rng, trials=300):
    V = set(range(n))
    quarters = []
    for p in P:
        p = sorted(p); rng.shuffle(p)
        quarters.append((set(p[:k//4]), set(p[k//4:])))
    pats = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]
    lines = [set(kappa) | set(p) for p in P]
    for _ in range(trials):
        sets = [set(l) for l in lines]
        for pt in pats:
            req = set()
            for i in range(3): req |= quarters[i][pt[i]]
            pad = list(V - req); rng.shuffle(pad)
            req |= set(pad[:T-len(req)])
            rest = list(V - req); rng.shuffle(rest)
            sets.append(req | set(rest[:n-k-len(req)]))
        assert all(len(s) == n-k for s in sets)
        cov = set()
        for s in sets:
            for a, b in itertools.combinations(sorted(s), 2): cov.add((a, b))
        if len(cov) != comb(n, 2): return False
    return True

def part_H2():
    print("== H end-to-end: Kleitman set + one half => pencil => good seven (55.2) ==")
    rng = random.Random(5)
    k, T, n = 8, 6, 16
    g = 12; hh = 4
    kappa = list(range(n-g)); ground = list(range(n-g, n))
    halves = list(itertools.combinations(ground, hh))
    S = {c for c in halves if ground[0] not in c}
    extra = [c for c in halves if ground[0] in c]
    bad = 0; tested = 0
    for ex in rng.sample(extra, 20):
        S2 = S | {ex}
        found = None
        for A in S2:
            rest = [x for x in ground if x not in A]
            for b in itertools.combinations(rest, hh):
                C = tuple(x for x in rest if x not in b)
                if b in S2 and C in S2: found = (A, b, C); break
            if found: break
        assert found is not None
        tested += 1
        if not finish_55_2(k, n, T, kappa, found, rng, trials=50): bad += 1
    print("(8,6,16) tested", tested, "bad", bad)
    k, T, n = 12, 9, 25
    kappa = list(range(n-18)); P = [list(range(n-18+6*i, n-18+6*i+6)) for i in range(3)]
    print("k=12 completion ok:", finish_55_2(k, n, T, kappa, P, rng, trials=100))
    # T = 3k/4 exactly, replies of minimal freedom; and negative control with only 3 patterns
    k, T, n = 8, 6, 16
    kappa = list(range(4)); P = [list(range(4+4*i, 8+4*i)) for i in range(3)]
    print("control: dropping pattern 110 must fail:")
    # quick direct check of the pair-cover logic
    qs = {}
    pats = [(0,0,0),(0,1,1),(1,0,1)]
    miss = 0
    for i, j in [(0,1),(0,2),(1,2)]:
        for a in (0,1):
            for b in (0,1):
                if not any(p[i]==a and p[j]==b for p in pats): miss += 1
    print("   uncovered quarter-pairs with 3 patterns:", miss)

def greedy_reply(S, order, om):
    un = [x for x in order if x not in S]
    return S | set(un[:om])

def part_W():
    print("== W as special case of H (star hitting), verbatim greedy rule; 55.1 criterion ==")
    rng = random.Random(99)
    k, T, n = 8, 6, 16; om = n-k-T; V = list(range(n))
    fails = 0; tot = 0
    for trial in range(300):
        R = rng.choice([2, 3, 8])
        orders = []
        for _ in range(R):
            o = V[:]; rng.shuffle(o); orders.append(o)
        wsz = rng.choice([0, 1, 2])  # T - k/2 = 2
        W = rng.sample(V, wsz)
        table = {}
        def sigma(S):
            key = tuple(sorted(set(S) & set(W)))
            if key not in table: table[key] = rng.randrange(R)
            return table[key]
        r = sigma(set(W))
        o = orders[r]
        J = []; cnt = 0
        for x in o:
            J.append(x)
            if x not in W: cnt += 1
            if cnt == om: break
        kap = set(J) | set(W)
        assert len(kap) <= n-3*k//2
        for x in V:
            if len(kap) == n-3*k//2: break
            kap.add(x)
        Z = [x for x in J if x not in W][:om]
        rest = [x for x in V if x not in kap]
        members = 0; allh = 0
        for P in itertools.combinations(rest, k//2):
            S = (kap | set(P)) - set(Z)
            assert len(S) == T
            rep = greedy_reply(S, orders[sigma(S)], om)
            allh += 1; members += (rep == kap | set(P))
        tot += 1; fails += (members != allh)
    print("windowed rules tested", tot, "kernels with a non-member line:", fails)
    mism = 0; chk = 0
    R = 3; orders = []
    for _ in range(R):
        o = V[:]; rng.shuffle(o); orders.append(o)
    sig = {}
    def sg(S):
        if S not in sig: sig[S] = rng.randrange(R)
        return sig[S]
    for tt in range(1500):
        K = frozenset(rng.sample(V, n-k))
        defm = any(frozenset(greedy_reply(set(S), orders[sg(frozenset(S))], om)) == K for S in itertools.combinations(sorted(K), T))
        crit = False
        for c in range(R):
            J = 0
            for x in orders[c]:
                if x in K: J += 1
                else: break
            for Z in itertools.combinations(orders[c][:J], om):
                if sg(K - frozenset(Z)) == c: crit = True; break
            if crit: break
        chk += 1; mism += (crit != defm)
    print("55.1 criterion checks", chk, "mismatches", mism)

if __name__ == '__main__':
    which = sys.argv[1:] or ['A', 'B2', 'H', 'H2', 'W', 'B']
    for w in which:
        {'A': part_A, 'B': part_B, 'B2': part_B2, 'H': part_H, 'H2': part_H2, 'W': part_W}[w]()
