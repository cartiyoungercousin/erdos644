r"""k = 8, W = 7 + 7 (n = 14 = 7k/4): E = 8-sets with |B n W1| odd.  Exact (7,2) via the Y-encoding SAT
(at most 7 members whose complements cover all 91 pairs), plus tau in {5,6,7} decided exactly by enumeration."""
import itertools, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
import sys
k, w1, w2 = 8, 7, 7; n = 14
par = None if sys.argv[1] == 'N' else int(sys.argv[1])
M = [frozenset(B) for B in itertools.combinations(range(n), k) if par is None or sum(1 for x in B if x < w1) % 2 == par]
t0 = time.time()
def is_transversal(Mset):
    U = frozenset(range(n)) - Mset
    return not any(B <= U for B in M)
for m in (5, 6, 7):
    ex = any(is_transversal(frozenset(Q)) for Q in itertools.combinations(range(n), m))
    print(f"par={par}: transversal of size {m} exists: {ex}", flush=True)
    if ex: break
comp = [frozenset(range(n)) - B for B in M]
cl = [[i + 1 for i in range(len(M)) if a in comp[i] and b in comp[i]] for a in range(n) for b in range(a + 1, n)]
card = CardEnc.atmost(lits=list(range(1, len(M) + 1)), bound=7, top_id=len(M), encoding=EncType.seqcounter)
with Solver(name='cadical153', bootstrap_with=cl + card.clauses) as S:
    r = S.solve()
    if r:
        B7 = [M[l - 1] for l in S.get_model() if 0 < l <= len(M)]
        ok = not any(all((a in B) or (b in B) for B in B7) for a in range(n) for b in range(a, n))
        print(f"par={par}: |H|={len(M)} NOT (7,2): seven verified={ok}  {time.time()-t0:.1f}s")
    else:
        print(f"par={par}: |H|={len(M)} (7,2): UNSAT exact  {time.time()-t0:.1f}s")
