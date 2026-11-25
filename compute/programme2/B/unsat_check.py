r"""Exact analysis of the route-3 instances where (H0)+(H1) hold, V = union H, and no Fano-type good seven exists:
any good seven (SAT, 'any' mode), tau(H) by exhaustive search, and the covering parameters."""
import sys, os, json, itertools
sys.path.insert(0, os.path.dirname(__file__))
from fam import coset_from_columns
from core import evenise, popc
from sat_check import good_seven_sat
for line in open(os.path.join(os.path.dirname(__file__), 'logs', 'route3_unsat.jsonl')):
    r = json.loads(line); n, k, M = r['n'], r['k'], r['M']
    cs0 = coset_from_columns(n, r['cols'], M, r['alpha']); cs = evenise(cs0, k)
    mem = [S for S in (sum(1 << x for x in c) for c in itertools.combinations(range(n), k)) if cs.syn(S) == cs.alpha]
    tau = next(t for t in range(n + 1) if any(all(S & sum(1 << x for x in X) for S in mem) for X in itertools.combinations(range(n), t)))
    st, _ = good_seven_sat(cs, k, mode='any')
    print(dict(n=n, k=k, M=M, cells=r['cells'], members=len(mem), tau=tau, T=tau - 1, three_k_over_4=0.75 * k,
               N=round(n / k, 3), fano='UNSAT', any=st, cols=r['cols'], alpha=r['alpha']))
