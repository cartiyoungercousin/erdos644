r"""Task 3(1): structure of the deletion-minimal templates. [computed exact]
 - member size distribution, profile counts vs covering lower bounds per class, degrees;
 - class decomposition check: every 13-set W contains members of at most one edge profile (parity) [proved by hand,
   re-checked here on the explicit family];
 - the literal (Sigma)(b) pencil of SATURATION 1.4 (co-edges (7,3),(7,3),(1,10), union V, kappa = 4): count.
Usage: py -3.14 structure.py FAMILY.npy"""
import sys, itertools, numpy as np
from math import comb
from collections import Counter, defaultdict
n, nX = 22, 12; FULL = (1 << n) - 1; Xm = (1 << nX) - 1
fam = [int(b) for b in np.load(sys.argv[1])]
pc = lambda m: bin(m).count('1')
prof = lambda B: (pc(B & Xm), pc(B >> nX))
P = Counter(prof(B) for B in fam)
print("members", len(fam), "| size distribution", dict(Counter(pc(B) for B in fam)), "| total size", sum(map(pc, fam)))
for p, v in sorted(P.items()):
    j, b = p
    if pc(Xm) and p[0] + p[1] == 12:
        lbY = comb(12, j) * comb(10, b + 1) / (10 - b) if b < 10 else 0     # 13-sets (j, b+1), each member covers 10-b
        lbX = comb(12, j + 1) * comb(10, b) / (12 - j) if j < 12 else 0     # 13-sets (j+1, b), each member covers 12-j
        print(f"  profile {p}: kept {v} of {comb(12, j) * comb(10, b)}; covering lower bound max({lbY:.0f}, {lbX:.0f})")
    else: print(f"  profile {p}: kept {v}")
deg = [sum(1 for B in fam if B >> p & 1) for p in range(n)]
print("degree X min/max", min(deg[:nX]), max(deg[:nX]), "| Y min/max", min(deg[nX:]), max(deg[nX:]))
# class decomposition
owner = defaultdict(set)
for B in fam:
    out = [p for p in range(n) if not B >> p & 1]
    for c in itertools.combinations(out, 13 - pc(B)): owner[B | sum(1 << p for p in c)].add(prof(B))
mixed = sum(1 for w, s in owner.items() if len(s) > 1)
print("13-sets covered:", len(owner), "of", comb(22, 13), "| 13-sets containing members of >1 profile:", mixed,
      dict(Counter(tuple(sorted(s)) for s in owner.values() if len(s) > 1)))
# literal pencil (7,3),(7,3),(1,10)
co = [FULL & ~B for B in fam]
c73 = defaultdict(list)
for K in co:
    if (pc(K & Xm), pc(K >> nX)) == (7, 3): c73[K >> nX].append(K & Xm)
tri = set(K for K in co if (pc(K & Xm), pc(K >> nX)) == (1, 10))
cnt = 0; ex = None
for yp, xs in c73.items():
    for a, b in itertools.combinations(xs, 2):
        if (a | b) == Xm and pc(a & b) == 2:
            for x in range(nX):
                if (a & b) >> x & 1 and ((1 << x) | (Xm ^ Xm) | (((1 << 10) - 1) << nX)) in tri:
                    cnt += 1; ex = ex or (a | yp << nX, b | yp << nX, x)
print("literal pencils ((7,3),(7,3),(1,10), union V, kappa = 4):", cnt, "example", ex)
