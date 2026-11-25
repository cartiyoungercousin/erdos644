r"""Task 3(1), uniform variant (MINIMAL_FRAME Lemmas 3U/4U).  U1 = G' padded: every 11-member X - x of G' gets its
own fresh point f_x = 22 + x, so U1 is 12-uniform on 34 points.  (7,2) and tau = 10 follow from G' by Lemma 1/
supersets [proved by hand]; here we test the fresh-point swap B -> B - z + z' for sampled incidences with deg z >= 2.
The swap is EXCLUDED iff there are six other members B2..B7 with (i) B - z, B2..B7 have no 2-point transversal in
V' (34 points) and (ii) no single point lies in all of B2..B7.  Candidates: transported profile certificates (as in
sat_transport.py), lifted to U1, then (i), (ii) checked by brute force over all points/pairs of V' [computed exact].
Misses are UNKNOWN.  Also re-checks the private sets of U1 exactly (13-set counts on the old points; a private set
never needs a fresh point, since a fresh point meets only its own member).
Usage: py -3.14 uniform_check.py GPRIME.npy NSAMPLE TRIES SEED"""
import sys, json, glob, re, itertools, numpy as np
from collections import defaultdict
n, nX, nV = 22, 12, 34; FULL = (1 << n) - 1; Xm = (1 << nX) - 1
G = [int(b) for b in np.load(sys.argv[1])]; ns, tries, seed = map(int, sys.argv[2:5]); rng = np.random.default_rng(seed)
pc = lambda m: bin(m).count('1')
lift = lambda B: B | (1 << (n + next(x for x in range(nX) if not B >> x & 1))) if pc(B) == 11 else B
U1 = [lift(B) for B in G]; assert all(pc(B) == 12 for B in U1)
coset = set(FULL & ~b for b in G)
certs = defaultdict(list)
for f in glob.glob('../saturation/logs/fkw_m3_shrunk_e*.log') + ['../saturation/logs/h1_saturation.log']:
    for line in open(f):
        m = re.search(r'(WITNESS|SEVEN) (\[\[.*?\]\])', line)
        if m:
            sv = [sum(1 << p for p in S) for S in json.loads(m.group(2))]
            certs[(pc(sv[0]), pc(sv[0] & Xm))].append(sv)
pts = lambda m_, N=n: [p for p in range(N) if m_ >> p & 1]
def transport(sv, Kp, iB):
    perm = [0] * n
    for side in (range(nX), range(nX, n)):
        a = [p for p in side if sv[0] >> p & 1] + [p for p in side if not sv[0] >> p & 1]
        c = list(rng.permutation([p for p in side if Kp >> p & 1])) + list(rng.permutation([p for p in side if not Kp >> p & 1]))
        for s_, t_ in zip(a, c): perm[s_] = int(t_)
    img = [sum(1 << perm[p] for p in pts(S)) for S in sv[1:]]
    return img if all(K in coset and K != FULL & ~G[iB] for K in img) else None
def lemma4U(Bz, others):  # Bz = B - z (in V'), others = six members of U1 (in V')
    sets = [Bz] + others
    no2 = not any(all(S >> a & 1 or S >> b & 1 for S in sets) for a in range(nV) for b in range(a, nV))
    noPt = not any(all(S >> a & 1 for S in others) for a in range(nV))
    return no2, noPt
# private sets of U1 (exact, old points)
W13 = {}
for i, B in enumerate(G):
    out = [p for p in range(n) if not B >> p & 1]
    for c in itertools.combinations(out, 13 - pc(B)): W13.setdefault(B | sum(1 << p for p in c), []).append(i)
print("13-sets covered", len(W13), "(all 497420 => tau(G') > 9, tau(U1) >= 10 by padding)")
haspriv = [False] * len(G)
for w, l in W13.items():
    if len(l) == 1: haspriv[l[0]] = True
print("every U1 member has a private set:", all(haspriv))
prof = lambda B: (pc(B & Xm), pc(B >> nX))
classes = defaultdict(list)
for i, B in enumerate(G):
    for side in 'XY':
        if (B & Xm if side == 'X' else B >> nX): classes[(prof(B), side)].append(i)
tot = defaultdict(int)
for key in sorted(classes):
    res = defaultdict(int)
    for _ in range(ns):
        i = int(rng.choice(classes[key])); B = G[i]
        z = int(rng.choice([p for p in pts(B) if (p < nX) == (key[1] == 'X')])); Kp = (FULL & ~B) | (1 << z)
        pool = certs.get((pc(Kp), pc(Kp & Xm)), []); verdict = 'UNKNOWN'
        for t in range(tries if pool else 0):
            img = transport(pool[t % len(pool)], Kp, i)
            if img is None: continue
            others = [lift(FULL & ~K) for K in img]
            no2, noPt = lemma4U(U1[i] & ~(1 << z), others)
            if no2 and noPt: verdict = 'SWAP_EXCLUDED'; break
            verdict = 'only (i)'
        res[verdict] += 1
    print(f"class {key[0]} z in {key[1]}: {dict(res)}", flush=True)
    for k_, v in res.items(): tot[k_] += v
print("TOTAL", dict(tot))
