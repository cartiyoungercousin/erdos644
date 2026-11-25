"""Sanity check of Lemma FW (notes/PROGRAMME4_PEN.md) on tiny cases: the largest family of k-subsets of [n]
with no two members meeting in exactly k-p points (p prime, (k+1)/2 <= p <= k) versus sum_{i<p} C(n,i).
Exact maximum via MaxSAT (RC2).  Usage: py -3.14 lemma_brute.py
"""
import itertools
from math import comb
from pysat.formula import WCNF
from pysat.examples.rc2 import RC2

cases = [(7, 3, 2), (8, 3, 2), (8, 4, 3), (9, 4, 3), (9, 5, 3), (10, 5, 3), (10, 4, 3), (11, 5, 3)]
for n, k, p in cases:
    l = k - p
    sets = [sum(1 << e for e in c) for c in itertools.combinations(range(n), k)]
    w = WCNF()
    for i in range(len(sets)):
        w.append([i + 1], weight=1)
    for a, b in itertools.combinations(range(len(sets)), 2):
        if bin(sets[a] & sets[b]).count("1") == l:
            w.append([-(a + 1), -(b + 1)])
    with RC2(w) as s:
        m = s.compute()
        best = sum(1 for v in m if v > 0)
    bound = sum(comb(n, i) for i in range(p))
    print(f"n={n} k={k} p={p} (forbidden |x&y|={l}): max family {best}, FW bound {bound}, "
          f"C(n,k)={comb(n,k)}  {'OK' if best <= bound else 'VIOLATION'}", flush=True)
