"""Exact-intersection gap search (programme 4, PEN).
Is there a k-uniform family on [n], (k+r)-covering (every (k+r)-set contains a member), with no two
members meeting in exactly l points?  Frankl-Rodl says: not for k large, r <= c0*k, l = floor((k-r)/2)
(see notes/PROGRAMME4_PEN.md, Theorem F).  Small sizes are far from that regime; this is a sanity probe.
Usage: py -3.14 exact_sat.py n k r [l=L] [t=SECONDS]      (default L = floor((k-r)/2), t = 600)
If SAT, the family is re-verified (covering and spectrum) independently of the solver.
"""
import sys, itertools, threading, time
from pysat.solvers import Cadical153

n, k, r = map(int, sys.argv[1:4])
opt = dict(a.split("=") for a in sys.argv[4:])
l = int(opt.get("l", (k - r) // 2))
tmo = float(opt.get("t", 600))
sets = list(itertools.combinations(range(n), k))
idx = {s: i + 1 for i, s in enumerate(sets)}
masks = [sum(1 << e for e in s) for s in sets]
S = Cadical153()
for A in itertools.combinations(range(n), k + r):
    S.add_clause([idx[c] for c in itertools.combinations(A, k)])
npair = 0
# pairs meeting in exactly l points: x, then choose l points of x and k-l points outside x
for a, s in enumerate(sets):
    out = [p for p in range(n) if p not in s]
    for I in itertools.combinations(s, l):
        for O in itertools.combinations(out, k - l):
            b = idx[tuple(sorted(I + O))] - 1
            if b > a:
                S.add_clause([-(a + 1), -(b + 1)]); npair += 1
t0 = time.time()
timer = threading.Timer(tmo, S.interrupt); timer.start()
res = S.solve_limited(expect_interrupt=True)
timer.cancel()
msg = f"n={n} k={k} r={r} forbidden |x&y|={l}: "
if res is None:
    msg += f"UNDECIDED ({tmo:.0f} s limit)"
elif res:
    fam = [masks[v - 1] for v in S.get_model() if v > 0]
    for A in itertools.combinations(range(n), k + r):
        mA = sum(1 << e for e in A)
        assert any(f & mA == f for f in fam)
    spec = sorted({bin(x & y).count("1") for x, y in itertools.combinations(fam, 2)})
    assert l not in spec
    msg += f"GAP FAMILY EXISTS, {len(fam)} members, spectrum {spec} (re-verified)"
else:
    msg += "NONE (UNSAT)"
print(msg + f"  [{len(sets)} sets, {npair} pair clauses, {time.time()-t0:.1f} s]", flush=True)
