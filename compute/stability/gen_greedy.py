r"""Method A: random greedy.  Random order of all k-sets; add if (7,2) still holds.  The check (exact DFS: no <=6 members cover,
with the new set, all pairs) is run to completion under a node limit; hitting the limit means REJECT, so every accepted
set is exactly certified and the final family is (7,2).  Final re-certification is done in analyze.py."""
import sys, time, random
from common import *
from pc72 import greedy_extend
def greedy(n, k, seed, node_limit=200000):
    rng = np.random.default_rng(seed); allS = sets_of_size(n, k); rng.shuffle(allS)
    return greedy_extend(allS, n, None, node_limit=node_limit)
if __name__ == '__main__':
    n, k, seed = map(int, sys.argv[1:4]); t = time.time()
    H = greedy(n, k, seed, int(sys.argv[4]) if len(sys.argv) > 4 else 200000)
    print(n, k, seed, len(H), 'tau', tau_ilp(H, n), round(time.time() - t, 1), flush=True)
    save_family(f'greedy_n{n}_k{k}_s{seed}', H, n, dict(method='greedy', k=k, seed=seed))
