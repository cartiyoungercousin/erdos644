r"""CORE 56: greedy rules with hash-like and structured selectors at finite k.  Exact: the rule is applied verbatim to real sets,
the seven replies are the rule's own replies, and all pairs of V are checked by brute force.
Her search uses the rule only through queries: random class r, random prefix I of its order (omega <= |I| <= n - 3k/2), kernel
kappa >= I, random petals; for each line K = kappa + P_i she tries holes Z in J_c(K) (prefix of order c inside K, 55.1) for
random classes c and keeps the line if reply(K - Z) == K.  Three lines -> four transversal requests (Theorem C / 55.2).
Usage: py hash_check.py [trials]
"""
import random, sys, hashlib, itertools

TRANS = [(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)]

class Rule:
    def __init__(self, n, k, T, orders, sel):
        self.n, self.k, self.T, self.om = n, k, T, n - k - T
        self.orders = orders; self.sel = sel; self.q = 0
        self.pos = [{x: i for i, x in enumerate(o)} for o in orders]
    def head(self, c, S):
        out = []
        for x in self.orders[c]:
            if x not in S:
                out.append(x)
                if len(out) == self.om: break
        return out
    def reply(self, S):
        assert len(S) == self.T
        self.q += 1
        return frozenset(S) | frozenset(self.head(self.sel(self, S), S))

def hv(S, salt):
    return int.from_bytes(hashlib.blake2b(bytes(sorted(S)) + salt, digest_size=8).digest(), 'big')

def make_selector(kind, n, k, T, R, rng):
    om = n - k - T; salt = bytes([rng.randrange(256) for _ in range(8)])
    if kind == "hash":                      # independent uniform class for every request
        return lambda rule, S: hv(S, salt) % R
    if kind == "linear":                    # additive hash: sum of random weights mod p, reduced mod R (pairwise independent)
        p = 1000003; a = [rng.randrange(p) for _ in range(n)]; b = rng.randrange(p)
        return lambda rule, S: ((sum(a[x] for x in S) + b) % p) % R
    if kind == "parity":                    # parity vector on R-1 random sets (R a power of 2 is not needed: index mod R)
        Es = [set(rng.sample(range(n), n // 2)) for _ in range(max(1, R.bit_length() - 1))]
        return lambda rule, S: sum((len(S & E) & 1) << i for i, E in enumerate(Es)) % R
    if kind in ("early", "late"):           # anti-plan thresholds: the class whose head ends earliest / latest in its own order
        def f(rule, S):
            e = [rule.pos[c][rule.head(c, S)[-1]] for c in range(R)]
            return e.index(min(e) if kind == "early" else max(e))
        return f
    if kind == "early^hash":                # threshold composed with a hash bit of the request (cyclic shift of the class)
        def f(rule, S):
            e = [rule.pos[c][rule.head(c, S)[-1]] for c in range(R)]
            return (e.index(min(e)) + hv(S, salt)) % R
        return f
    if kind == "junta+":                    # min-junta on a window of T - k/2 + 1 points (one more than Theorem W allows); R = window+1
        W = rng.sample(range(n), T - k // 2 + 1)
        def f(rule, S):
            for i, x in enumerate(W):
                if x not in S: return i % R
            return len(W) % R
        return f
    if kind == "midhash":                   # class = hash of the request outside the two length-L prefixes, flipped by an anti-plan bit
        L = n - 3 * k // 2
        def f(rule, S):
            zones = [set(o[:L]) for o in rule.orders[:2]]
            u = [len(z - S) for z in zones]
            mid = frozenset(S) - zones[0] - zones[1]
            return (hv(mid, salt) + (u[0] <= u[1])) % 2 if R == 2 else (hv(mid, salt) + u[0]) % R
        return f
    raise ValueError(kind)

def J(rule, c, K):
    out = []
    for x in rule.orders[c]:
        if x in K: out.append(x)
        else: break
    return out

def solve(rule, rng, max_frames=400, tries=60):
    n, k, T, om = rule.n, rule.k, rule.T, rule.om; R = len(rule.orders); ker = n - 3 * k // 2
    for fr in range(max_frames):
        r = rng.randrange(R); al = rng.randint(om, ker) if rng.random() < 0.7 else om
        I = rule.orders[r][:al]; rest = [x for x in range(n) if x not in set(I)]; rng.shuffle(rest)
        kap = set(I) | set(rest[:ker - al]); U = rest[ker - al:]
        petals = [U[:k // 2], U[k // 2:k], U[k:]]
        ok = True
        for P in petals:
            K = frozenset(kap | set(P)); got = False
            cands = [(c, J(rule, c, K)) for c in range(R)]; cands = [(c, j) for c, j in cands if len(j) >= om]
            for _ in range(tries):
                if not cands: break
                c, j = rng.choice(cands); Z = rng.sample(j, om)
                if rule.reply(K - set(Z)) == K: got = True; break
            if not got: ok = False; break
        if not ok: continue
        # the three lines are members (found as replies); finish with four transversal requests
        seven = [frozenset(kap | set(P)) for P in petals]
        halves = [(p[:k // 4], p[k // 4:]) for p in petals]
        for tr in TRANS:
            S = set(x for i in range(3) for x in halves[i][tr[i]])
            for x in range(n):
                if len(S) >= T: break
                S.add(x)
            seven.append(rule.reply(S))
        cover = all(any(x in K and y in K for K in seven) for x in range(n) for y in range(x, n))
        return fr + 1, cover
    return None, False

if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    rng = random.Random(644)
    sizes = [(40, 31, 74), (40, 31, 76), (40, 31, 80), (40, 31, 88), (100, 76, 180), (100, 76, 190), (100, 76, 210)]
    kinds = [("hash", 2), ("hash", 8), ("hash", 64), ("linear", 2), ("linear", 8), ("parity", 2), ("parity", 8), ("early", 2), ("early", 4),
             ("late", 2), ("late", 4), ("early^hash", 2), ("early^hash", 4), ("junta+", None), ("midhash", 2), ("midhash", 4)]
    tot = good = 0
    for (k, T, n) in sizes:
        for kind, R in kinds:
            RR = R if R else T - k // 2 + 2
            w = 0; fs = []; qs = []
            for _ in range(trials):
                for mode in ("rand", "rev"):
                    if mode == "rev" and RR != 2: continue
                    orders = [rng.sample(range(n), n) for _ in range(RR)]
                    if mode == "rev": orders[1] = orders[0][::-1]
                    rule = Rule(n, k, T, orders, make_selector(kind, n, k, T, RR, rng))
                    f, cover = solve(rule, rng, max_frames=(6000 if kind == "junta+" else 400), tries=(25 if kind == "junta+" else 60)); tot += 1
                    if cover: w += 1; good += 1; fs.append(f); qs.append(rule.q)
                    else: print(f"   FAIL k={k} T={T} n={n} {kind} R={RR} {mode} frames={f}", flush=True)
            print(f"k={k} T={T} n={n} {kind:10s} R={RR:3d}: good sevens {w}/{trials * (2 if RR == 2 else 1)}  "
                  f"median frames {sorted(fs)[len(fs)//2] if fs else '-'}  median queries {sorted(qs)[len(qs)//2] if qs else '-'}", flush=True)
    print(f"TOTAL good sevens {good}/{tot}")
