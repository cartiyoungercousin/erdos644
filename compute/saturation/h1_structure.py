r"""Structure of H1 (the saturated family reached from FKW m = 3 by greedy shrinking). [computed exact]
H1 = {12-sets A of V = X + Y (|X| = 12, |Y| = 10) with |A & X| in {3,5,7,9}} + {X - x : x in X}.
Prints: size, total size, degree profile, tau (exact, by profiles: a set misses every edge iff its complement contains
no edge; profile families make this a check over (|U & X|, |U & Y|)), antichain check, and the largest triple
intersection over co-edge triples with union V (the (Sigma)(b) pencil test needs kappa >= n - 2T = 4).
Usage: py -3.14 h1_structure.py"""
from math import comb
import itertools
nX, nY, n, T = 12, 10, 22, 9
E = [(j, 12 - j) for j in (3, 5, 7, 9)] + [(11, 0)]           # edge profiles (|A&X|, |A&Y|)
cnt = {p: comb(nX, p[0]) * comb(nY, p[1]) for p in E}
print("members", sum(cnt.values()), {p: cnt[p] for p in E}, "| total size", sum(cnt[p] * sum(p) for p in E))
degX = sum(cnt[p] * p[0] for p in E) // nX; degY = sum(cnt[p] * p[1] for p in E) // nY
print("degree of each X point", degX, "| of each Y point", degY)
# tau: max |U| such that U contains no edge; U of profile (a, b) contains an edge of profile p iff p <= (a, b)
best = max(a + b for a in range(nX + 1) for b in range(nY + 1) if not any(p[0] <= a and p[1] <= b for p in E))
print("tau =", n - best, "> T =", T)
print("antichain (no edge profile dominated by another distinct profile with smaller size):",
      not any(p != q and p[0] <= q[0] and p[1] <= q[1] for p in E for q in E))
# pencils: co-edge profiles
C = [(nX - a, nY - b) for a, b in E]
def cell_best(N, s):  # max r7 over Venn counts of 3 subsets of an N-cell with sizes s and empty region 0
    best = -1
    for comp in itertools.product(range(N + 1), repeat=7):  # regions 1..7
        pass
    return best
# exact small DP instead: regions 1..7 counts; sizes s_i = sum over regions containing i
from functools import lru_cache
def maxk(N, s):
    best = -1
    regs = list(range(1, 8))
    def rec(i, left, sz, r7):
        nonlocal best
        if i == 7:
            if left == 0 and list(sz) == list(s): best = max(best, r7)
            return
        r = regs[i]
        for x in range(left + 1):
            nsz = [sz[t] + (x if r >> t & 1 else 0) for t in range(3)]
            if any(nsz[t] > s[t] for t in range(3)): break
            rec(i + 1, left - x, nsz, r7 + (x if r == 7 else 0))
    rec(0, N, [0, 0, 0], 0); return best
kap = -1; arg = None
for tr in itertools.combinations_with_replacement(C, 3):
    kx = maxk(nX, [p[0] for p in tr]); ky = maxk(nY, [p[1] for p in tr])
    if kx >= 0 and ky >= 0 and kx + ky > kap: kap, arg = kx + ky, tr
print("max triple intersection over co-edge triples with union V:", kap, "at co-edge profiles", arg,
      "| pencil needs >=", n - 2 * T)
