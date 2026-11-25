"""Pair-level gap search: is there a k-uniform family on [n] in which every (k+r)-set contains a member
and no two members have |x & y| in the given set J?  (Lemma 5c says: impossible if J contains an
interval of w+1 integers with 2w+2 > r, under its size conditions.)
Usage: py -3.14 gap_sat.py n k r j1 [j2 ...]
"""
import sys, itertools
from pysat.solvers import Cadical153

n, k, r = map(int, sys.argv[1:4]); J = set(map(int, sys.argv[4:]))
sets = list(itertools.combinations(range(n), k))
idx = {s: i + 1 for i, s in enumerate(sets)}
masks = [sum(1 << e for e in s) for s in sets]
S = Cadical153()
for A in itertools.combinations(range(n), k + r):
    S.add_clause([idx[c] for c in itertools.combinations(A, k)])
npair = 0
for a in range(len(sets)):
    ma = masks[a]
    for b in range(a + 1, len(sets)):
        if bin(ma & masks[b]).count("1") in J:
            S.add_clause([-(a + 1), -(b + 1)]); npair += 1
res = S.solve()
msg = f"n={n} k={k} r={r} forbidden intersections {sorted(J)}: "
if res:
    model = set(v for v in S.get_model() if v > 0)
    fam = [masks[v - 1] for v in model]
    # verify independently
    for A in itertools.combinations(range(n), k + r):
        mA = sum(1 << e for e in A)
        assert any(f & mA == f for f in fam)
    spec = sorted({bin(x & y).count("1") for x, y in itertools.combinations(fam, 2)})
    msg += f"GAP FAMILY EXISTS, {len(fam)} members, intersection spectrum {spec} (covering re-verified)"
else:
    msg += "NONE (UNSAT)"
print(msg + f"  [{len(sets)} sets, {npair} pair clauses]")
