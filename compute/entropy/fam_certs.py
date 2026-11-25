r"""CORE 72: exact certificate census on a finite family of co-edges (default: core9 fam_8_6_15_rev).
(b) pencil-type triples: union = V and |K1 & K2 & K3| >= n - 2T.        (Σ)(b) as corrected in LEDGER
(a) Q' quadruples:  sigma <= (3T - n)/2 and, for each matching, pair-only mass + sigma <= T.
Also: point frequencies (uniform on the family, and reply law of uniform T-requests under the
"first member containing S" rule), entropies in nats.   [computed exact; entropies float]
Usage: py fam_certs.py k T n famfile
"""
import sys, itertools, math
import numpy as np
from collections import Counter
k, T, n = map(int, sys.argv[1:4]); fam = sys.argv[4]
M = []
for line in open(fam):
    s = line.split()
    if s: M.append(sum(1 << int(x) for x in s))
M = sorted(set(M)); m = len(M); c = n - k; full = (1 << n) - 1
assert all(bin(K).count("1") == c for K in M)
pc = lambda x: bin(x).count("1")
# superset lists for masks of size >= 1
sup = {}
for K in M:
    bits = [i for i in range(n) if K >> i & 1]
    for j in range(1, c + 1):
        for sub in itertools.combinations(bits, j):
            sup.setdefault(sum(1 << i for i in sub), []).append(K)
# T-covering check
unc = sum(1 for S in itertools.combinations(range(n), T) if sum(1 << i for i in S) not in sup)
print(f"family {fam}: {m} members of size {c}, n={n}, T-sets uncovered: {unc}")
# (b)
need3 = n - 2 * T; cntb = 0; best = None
for a in range(m):
    for b in range(a + 1, m):
        K1, K2 = M[a], M[b]; need = full & ~(K1 | K2); meet = K1 & K2
        cand = sup.get(need, []) if need else M
        for K3 in cand:
            if K3 > K2 and pc(K1 & K2 & K3) >= need3: cntb += 1
        # defect: best triple ignoring exactness
print(f"(b) triples (union V, triple meet >= {need3}): {cntb}")
# defect of (b) <= 1: d = |need - K3| + max(0, need3 - |meet & K3|); K3 must contain need minus <= 1 point
hist = Counter()
for a in range(m):
    K1 = M[a]
    for b in range(a + 1, m):
        K2 = M[b]; need = full & ~(K1 | K2); meet = K1 & K2
        subs = [need] + [need & ~(1 << i) for i in range(n) if need >> i & 1]
        seen = set()
        for sbm in subs:
            for K3 in (sup.get(sbm, []) if sbm else M):
                if K3 <= K2 or K3 in seen: continue
                seen.add(K3)
                d = pc(need & ~K3) + max(0, need3 - pc(meet & K3))
                if d <= 1: hist[d] += 1
print(f"(b) defect census over all triples: defect 0: {hist[0]}, defect 1: {hist[1]} (none listed means >= 2)")
# (a) Q' quadruples via base-3 pair keys
w3 = np.array([3 ** i for i in range(n)], dtype=np.int64)
vec = np.array([[K >> i & 1 for i in range(n)] for K in M], dtype=np.int64)
key = vec @ w3
ia, ib = np.triu_indices(m, 1)
pk = key[ia] + key[ib]
from collections import defaultdict
idx = defaultdict(list)
for p, x in enumerate(pk.tolist()): idx[x].append(p)
twos = 2 * int(w3.sum()); sig_max = (3 * T - n) / 2
nq = 0; ngood = 0
for p, x in enumerate(pk.tolist()):
    v = vec[ia[p]] + vec[ib[p]]
    for z in range(n):
        if v[z] != 0: continue
        tgt = twos - 2 * 3 ** z - x
        for q in idx.get(tgt, []):
            if q <= p: continue
            Ks = [M[ia[p]], M[ib[p]], M[ia[q]], M[ib[q]]]
            mult = [sum(K >> i & 1 for K in Ks) for i in range(n)]
            sigma = sum(1 for u in mult if u <= 1)
            if sigma > sig_max: continue
            nq += 1
            ok = True
            for (i1, i2), (i3, i4) in [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]:
                po = sum(1 for i in range(n) if mult[i] == 2 and ((Ks[i1] & Ks[i2]) >> i & 1 or (Ks[i3] & Ks[i4]) >> i & 1))
                if po + sigma > T: ok = False
            ngood += ok
print(f"(a) quadruples with sigma <= {sig_max} (each counted once per split): {nq}; with all three matchings OK: {ngood}")
# frequencies and entropies
freq = vec.mean(0); print("point frequencies (uniform on family): min %.4f max %.4f (c/n = %.4f)" % (freq.min(), freq.max(), c / n))
rep = Counter()
for S in itertools.combinations(range(n), T):
    ms = sum(1 << i for i in S)
    if ms in sup: rep[min(sup[ms])] += 1
tot = sum(rep.values()); pr = np.array(list(rep.values())) / tot
H = -(pr * np.log(pr)).sum()
f2 = np.zeros(n)
for K, w in rep.items():
    for i in range(n):
        if K >> i & 1: f2[i] += w / tot
print(f"reply law (min-mask rule): support {len(rep)}, H = {H:.4f}, log|family| = {math.log(m):.4f}, "
      f"log C(n,T)-log C(c,T) = {math.log(math.comb(n,T)/math.comb(c,T)):.4f}; freq min {f2.min():.4f} max {f2.max():.4f}")
