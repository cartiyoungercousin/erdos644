r"""CORE 55.5, second SAT formulation, split into 5 sub-cases (run in parallel).
In a cover of the pairs of 15 points by seven 7-sets every point has r_x >= 3 and sum (r_x - 3) = 4, so among the points
0..4 some x has r_x = 3 exactly [proved by hand].  Sub-case x: exactly 7 members chosen, every pair covered, every point in
>= 3 chosen, point x in exactly 3 chosen.  The family has a good seven iff some sub-case is SAT.
Usage: py seven_split.py famfile n x"""
import sys, itertools, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
fam = [frozenset(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]; n = int(sys.argv[2]); x0 = int(sys.argv[3])
m = len(fam); lits = list(range(1, m + 1)); cl = []; top = m
def add(enc):
    global top; cl.extend(enc.clauses); top = max(top, enc.nv)
for x, y in itertools.combinations(range(n), 2): cl.append([i + 1 for i, K in enumerate(fam) if x in K and y in K])
add(CardEnc.equals(lits=lits, bound=7, top_id=top, encoding=EncType.totalizer))
for x in range(n):
    lx = [i + 1 for i, K in enumerate(fam) if x in K]
    add(CardEnc.atleast(lits=lx, bound=3, top_id=top, encoding=EncType.totalizer))
    if x == x0: add(CardEnc.atmost(lits=lx, bound=3, top_id=top, encoding=EncType.totalizer))
t0 = time.time(); s = Cadical153(bootstrap_with=cl); ok = s.solve()
if ok:
    ch = [fam[v - 1] for v in s.get_model() if 0 < v <= m]
    good = all(any(a in K and b in K for K in ch) for a, b in itertools.combinations(range(n), 2))
    print(f"x={x0}: SAT, seven = {[sorted(K) for K in ch]}, pairs check {good} ({time.time()-t0:.0f}s)")
else: print(f"x={x0}: UNSAT [exact] ({time.time()-t0:.0f}s)")
