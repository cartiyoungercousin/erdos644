r"""Task 3(1): saturation certificates for incidences (z, B) of a deletion-minimal (non-symmetric) family, by
TRANSPORTING the exact profile-level sevens of compute/saturation (H1 and FKW m = 3 classes) with random
pi in Sym(X) x Sym(Y) mapping the certificate's 11/12-set K'_0 onto K' = (V - B) + {z}.  A hit (all six other
co-edges are co-edges of members of the family, none equal to K_B) is a saturation certificate, re-checked by plain
code (pair cover) [computed exact].  A miss after the try budget is UNKNOWN, not loose.
Lemma 4U (uniform variant) needs in addition: the six other co-edges have union V (no point lies in all six other
members); the flag 'U' records whether the found seven also satisfies this (so the fresh-point swap is excluded).
Usage: py -3.14 sat_transport.py FAMILY.npy NSAMPLE TRIES SEED"""
import sys, json, glob, numpy as np, re
from collections import defaultdict
n, nX = 22, 12; FULL = (1 << n) - 1; Xm = (1 << nX) - 1
fam = [int(b) for b in np.load(sys.argv[1])]; ns, tries, seed = map(int, sys.argv[2:5])
coset = set(FULL & ~b for b in fam)
rng = np.random.default_rng(seed)
certs = defaultdict(list)   # (|K'0|, |K'0 & X|) -> list of seven (bitmasks), first = K'0
for f in glob.glob('../saturation/logs/fkw_m3_shrunk_e*.log') + ['../saturation/logs/h1_saturation.log']:
    for line in open(f):
        m = re.search(r'(WITNESS|SEVEN) (\[\[.*?\]\])', line)
        if not m: continue
        sv = [sum(1 << p for p in S) for S in json.loads(m.group(2))]
        assert all(any(S >> u & 1 and S >> v & 1 for S in sv) for u in range(n) for v in range(u, n))
        K0 = sv[0]; certs[(bin(K0).count('1'), bin(K0 & Xm).count('1'))].append(sv)
pts = lambda m_: [p for p in range(n) if m_ >> p & 1]
def transport(sv, Kp, iB):
    K0 = sv[0]; perm = [0] * n
    for side in (range(nX), range(nX, n)):
        a = [p for p in side if K0 >> p & 1]; b = [p for p in side if not K0 >> p & 1]
        c = [p for p in side if Kp >> p & 1]; d = [p for p in side if not Kp >> p & 1]
        c = list(rng.permutation(c)); d = list(rng.permutation(d))
        for s_, t_ in zip(a + b, c + d): perm[s_] = int(t_)
    img = [sum(1 << perm[p] for p in pts(S)) for S in sv[1:]]
    if all(K in coset and K != FULL & ~fam[iB] for K in img): return img
    return None
prof = lambda B: (bin(B & Xm).count('1'), bin(B >> nX).count('1'))
classes = defaultdict(list)
for i, B in enumerate(fam):
    for side in 'XY':
        if (B & Xm if side == 'X' else B >> nX): classes[(prof(B), side)].append(i)
tot = defaultdict(int)
for key in sorted(classes):
    res = defaultdict(int)
    for _ in range(ns):
        i = int(rng.choice(classes[key])); B = fam[i]
        z = int(rng.choice([p for p in pts(B) if (p < nX) == (key[1] == 'X')])); Kp = (FULL & ~B) | (1 << z)
        pool = certs.get((bin(Kp).count('1'), bin(Kp & Xm).count('1')), [])
        found = None
        for t in range(tries if pool else 0):
            img = transport(pool[t % len(pool)], Kp, i)
            if img: found = img; break
        if found is None: res['UNKNOWN'] += 1; continue
        seven = [Kp] + found
        assert all(any(S >> u & 1 and S >> v & 1 for S in seven) for u in range(n) for v in range(u, n))
        U = (found[0] | found[1] | found[2] | found[3] | found[4] | found[5]) == FULL
        res['SAT+U' if U else 'SAT(not U)'] += 1
    print(f"class edge-profile {key[0]} z in {key[1]} (certs {len(certs.get((n-sum(key[0])+1, nX-key[0][0]+(key[1]=='X')),[]))}): {dict(res)}", flush=True)
    for k_, v in res.items(): tot[k_] += v
print("TOTAL", dict(tot))
