"""Integer B-load check for PS2 (PETAL §27.3): all integer B-structures with petal budgets <= d; max over them of the least
integer max-load (MIP of ps2.design over S-choices).  Usage: py intload.py d"""
import sys, os, itertools
sys.path.insert(0, os.path.dirname(__file__))
from bload_lp import TYPES
from ps2 import design
d = int(sys.argv[1])
worst, arg, cnt = -1, None, 0
def rec(i, budget, m):
    global worst, arg, cnt
    if i == len(TYPES):
        cnt += 1
        counts = {J: c for J, c in zip(TYPES, m) if c}
        best = min(v for s1 in (None, 0, 1, 2) for s2 in (None, 3) for r in [design(counts, s1, s2)] if r is not None for v in [r[1]])
        if best > worst: worst, arg = best, dict(counts)
        return
    J = TYPES[i]
    cap = min(budget[a] for a in J)
    for c in range(cap + 1):
        b2 = list(budget)
        for a in J: b2[a] -= c
        rec(i + 1, b2, m + [c])
rec(0, [d] * 4, [])
print("d=%d: %d integer structures; worst least max B-load = %g (2d = %d) at %s" % (d, cnt, worst, 2 * d, {"".join(str(a + 1) for a in sorted(J)): c for J, c in arg.items()}))
