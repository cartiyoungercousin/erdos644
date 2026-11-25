r"""Task 3(1): deletion-minimalisation of H1 (SATURATION 1.3-1.4). [computed exact]
V = X + Y, X = bits 0..11, Y = bits 12..21. H1 = {12-sets A, |A & X| in {3,5,7,9}} + {X - x}.  T = 9, tau(H1) = 10.
Lemma 3 test, exact: a member B has a private set (a set S, |S| <= 9, S disjoint from B, meeting every other member)
iff some 13-set W containing B contains no OTHER member (take S = V - W; enlarging S within V - B only helps, and
|V - B| >= 10 > 9).  So with cnt[W] = #members inside W:  B private  <=>  exists W > B, |W| = 13, cnt[W] = 1.
tau(H) > 9 <=> every 13-set W contains a member (cnt[W] >= 1).
Deleting B keeps tau > 9 iff B has no private set; (7,2) is inherited by subfamilies.  A member that has a private set
keeps it after other deletions (cnt[W] = 1 with B inside W stays 1).  So ONE pass in any order ends deletion-minimal.
Usage: py -3.14 minimize_h1.py ORDER SEED [h1|fkw]   (fkw: the uniform FKW family at m = 3; j = 1 is excluded since |Y| = 10 < 11)
     ORDER in {random, prof:<j1>,<j2>,...} (profiles deleted first in that order)
Writes out/h1min_<ORDER>_<SEED>.npy (kept member bitmasks)."""
import sys, itertools, numpy as np, time
from math import comb
n, nX = 22, 12
X = (1 << nX) - 1; FULL = (1 << n) - 1
order_kind = sys.argv[1]; seed = int(sys.argv[2]); base = sys.argv[3] if len(sys.argv) > 3 else 'h1'
t0 = time.time()
def masks(points, r):
    for c in itertools.combinations(points, r): yield sum(1 << p for p in c)
mem = []
for j in ((3, 5, 7, 9) if base == 'h1' else (3, 5, 7, 9, 11)):
    for a in masks(range(nX), j):
        for b in masks(range(nX, n), 12 - j): mem.append(a | b)
if base == 'h1':
    for x in range(nX): mem.append(X & ~(1 << x))
mem = np.array(mem, dtype=np.int64); M = len(mem)
W13 = np.array(list(masks(range(n), 13)), dtype=np.int64); widx = {int(w): i for i, w in enumerate(W13)}
SUP = []
for B in mem:
    B = int(B); out = [p for p in range(n) if not B >> p & 1]; need = 13 - bin(B).count('1')
    SUP.append(np.array([widx[B | sum(1 << p for p in c)] for c in itertools.combinations(out, need)], dtype=np.int64))
cnt = np.zeros(len(W13), dtype=np.int32)
for s in SUP: cnt[s] += 1
assert cnt.min() >= 1, "H1 itself must have tau > 9"
jx = np.array([bin(int(B) & X).count('1') for B in mem])
rng = np.random.default_rng(seed); perm = rng.permutation(M)
if order_kind.startswith('prof:'):
    pri = [int(v) for v in order_kind[5:].split(',')]
    key = np.array([pri.index(j) if j in pri else len(pri) for j in jx])
    perm = perm[np.argsort(key[perm], kind='stable')]
keep = np.ones(M, bool)
for i in perm:
    s = SUP[i]
    if (cnt[s] == 1).any(): continue
    cnt[s] -= 1; keep[i] = False
K = mem[keep]
print(f"base={base} order={order_kind} seed={seed}: H1 {M} -> kept {keep.sum()} members ({time.time()-t0:.1f}s)")
np.save(f"out/{base}min_{order_kind.replace(':','').replace(',','-')}_{seed}.npy", K)
assert cnt.min() >= 1
# private-set re-check from the final counts
priv = [bool((cnt[SUP[i]] == 1).any()) for i in np.nonzero(keep)[0]]
print("every kept member has a private set:", all(priv), "| min cnt over 13-sets:", cnt.min())
from collections import Counter
prof = Counter((int(jx[i]), bin(int(mem[i])).count('1') - int(jx[i])) for i in np.nonzero(keep)[0])
print("kept edge profiles (|A&X|,|A&Y|): count / class size:",
      {p: f"{v}/{comb(12,p[0])*comb(10,p[1]) if p != (11,0) else 12}" for p, v in sorted(prof.items())})
from collections import Counter as C2
print("member size distribution:", dict(C2(bin(int(B)).count('1') for B in K)))
print("total size", sum(bin(int(B)).count('1') for B in K))
deg = [int(sum(1 for B in K if int(B) >> p & 1)) for p in range(n)]
print("degrees X:", deg[:nX]); print("degrees Y:", deg[nX:])
h = Counter(cnt.tolist()); print("cover multiplicity of 13-sets (cnt: #W):", dict(sorted(h.items())[:12]))
