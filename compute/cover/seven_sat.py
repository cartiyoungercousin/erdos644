r"""CORE 106: exact decision 'are there 7 members covering all pairs of V' by SAT (Cadical + seqcounter <= 7). [computed exact]
Usage: py seven_sat.py famfile n"""
import sys, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
fam = [frozenset(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]; n = int(sys.argv[2]); m = len(fam)
cnf = CardEnc.atmost(lits=list(range(1, m + 1)), bound=7, top_id=m, encoding=EncType.seqcounter)
s = Cadical153(bootstrap_with=cnf.clauses)
for x, y in itertools.combinations(range(n), 2):
    s.add_clause([i + 1 for i, K in enumerate(fam) if x in K and y in K])
ok = s.solve()
if ok:
    ch = [fam[v - 1] for v in s.get_model() if 0 < v <= m]
    assert len(ch) <= 7 and all(any(x in K and y in K for K in ch) for x, y in itertools.combinations(range(n), 2))
    print(f"{sys.argv[1]}: GOOD SEVEN (SAT, checked):", " ".join("{" + ",".join(map(str, sorted(K))) + "}" for K in ch))
else: print(f"{sys.argv[1]}: NO good seven (UNSAT, exact)")
