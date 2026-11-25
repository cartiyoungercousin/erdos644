r"""CORE 106: small covering designs C(n, n-k, T) for the exact census.  [computed exact]
kinds:  greedy  - random greedy: pick a uniformly random uncovered T-set, extend it by the w = n-k-T outside points
                  that cover the most uncovered T-sets (ties random); repeat until covering.
        nibble  - random: extend each uncovered T-set (random order) by w uniformly random outside points.
        minimal - then prune to an inclusion-minimal subfamily (random order); monotone, so this keeps 'no good seven'.
        sum     - {K : sum(K) mod m in A}, A = {0..a-1}, least a that covers  (algebraic, anti-Pasch style: membership by one linear hash)
        code    - {K : H x_K = 0 over F_2 } for a random r x n parity matrix H, r as large as covering allows
        code1   - the same with H 1_V != 0 (1_V not a codeword): then no three members have K1+K2+K3 = 1_V mod 2,
                  in particular no exact pencil (kernel triple, petals single)
Usage: py build_designs.py k T n kind seed out
"""
import sys, itertools, random
k, T, n = map(int, sys.argv[1:4]); kind = sys.argv[4]; seed = int(sys.argv[5]); out = sys.argv[6]
rng = random.Random(seed); c = n - k; w = c - T
msk = lambda S: sum(1 << i for i in S)
Tsets = [msk(S) for S in itertools.combinations(range(n), T)]
def subsT(K):
    b = [i for i in range(n) if K >> i & 1]
    return [msk(S) for S in itertools.combinations(b, T)]
def covering(fam):
    cov = set()
    for K in fam: cov.update(subsT(K))
    return len(cov) == len(Tsets)
def prune(fam):
    cnt = {}
    for K in fam:
        for S in subsT(K): cnt[S] = cnt.get(S, 0) + 1
    fam = list(fam); rng.shuffle(fam); keep = []
    for K in fam:
        ss = subsT(K)
        if all(cnt[S] > 1 for S in ss):
            for S in ss: cnt[S] -= 1
        else: keep.append(K)
    return keep
fam = set()
if kind in ("greedy", "nibble", "greedy_min", "nibble_min"):
    unc = set(Tsets); order = Tsets[:]; rng.shuffle(order)
    for S in order:
        if S not in unc: continue
        outs = [i for i in range(n) if not S >> i & 1]
        if kind.startswith("greedy"):
            best = []; bv = -1
            for D in itertools.combinations(outs, w):
                K = S | msk(D); v = sum(1 for X in subsT(K) if X in unc)
                if v > bv: bv, best = v, [K]
                elif v == bv: best.append(K)
            K = rng.choice(best)
        else: K = S | msk(rng.sample(outs, w))
        fam.add(K); unc.difference_update(subsT(K))
    if kind.endswith("_min"): fam = prune(fam)
elif kind.startswith("sum"):
    m = int(kind[3:]) if len(kind) > 3 else n
    allK = list(itertools.combinations(range(n), c))
    for a in range(1, m + 1):
        fam = {msk(K) for K in allK if sum(K) % m < a}
        if covering(fam): print(f"sum: m = {m}, A = {{0..{a-1}}}"); break
elif kind.startswith("code"):
    allc = [msk(K) for K in itertools.combinations(range(n), c)]
    for r in range(12, 0, -1):
        found = False
        for tr in range(30):
            H = [rng.getrandbits(r) for _ in range(n)]
            def syn(K):
                s = 0
                for i in range(n):
                    if K >> i & 1: s ^= H[i]
                return s
            F = {K for K in allc if syn(K) == 0}
            if kind == "code1" and syn((1 << n) - 1) == 0: continue   # want 1_V outside the code
            if covering(F): fam = F; found = True; break
        if found: print(f"code: r = {r} parity checks"); break
assert covering(fam), "not T-covering"
with open(out, "w") as f:
    for K in sorted(fam): f.write(" ".join(str(i) for i in range(n) if K >> i & 1) + "\n")
print(f"{kind} k={k} T={T} n={n} seed={seed}: {len(fam)} members, T-covering, written {out}")
