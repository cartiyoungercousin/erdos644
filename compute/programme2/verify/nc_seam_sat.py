"""Exact (SAT / exhaustive) checks of the seam family E_k: k-subsets of W (|W|=7k/4) odd on W1."""
import itertools, sys, json
from nc_verify import good_seven, exhaustive_good7, tau, pc
def E(w1, w2, k):
    W1 = (1 << w1) - 1
    return [m for m in (sum(1 << v for v in S) for S in itertools.combinations(range(w1 + w2), k)) if pc(m & W1) % 2 == 1]
for w1, w2, k, how in json.loads(sys.argv[1]):
    H = E(w1, w2, k); V = (1 << (w1 + w2)) - 1
    g = exhaustive_good7(H, V) if how == "exh" else good_seven(H, V)
    print(json.dumps(dict(w1=w1, w2=w2, k=k, how=how, members=len(H), tau=tau(H, V), good7=g is not None)), flush=True)
