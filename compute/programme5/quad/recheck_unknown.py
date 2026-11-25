"""Re-run the scan's UNKNOWN class (dense random q at c = 10, 12) with fano_exact continuing past undecided d-vectors."""
import numpy as np, time
from qlib import *
rng = np.random.default_rng(11)
for (n, k) in [(20, 10), (24, 12)]:
    pc = popcount_arr(n); b = (3 * k + 5) // 4; done = 0
    while done < 6:
        G = random_graph(n, 0.5, rng); l = int(rng.integers(0, 1 << n)); qv = qtable(n, G, l)
        for a in (0, 1):
            tau, M = tau_levelset(n, k, qv, a, pc)
            if tau < b + 1: continue
            t0 = time.time()
            f, w, st = fano_exact(n, k, G, l, a, qv, n - k - tau + 1, budget=2_000_000, tries=20000)
            if w: assert check_seven(w, n) and all(qv[B] == a and bin(B).count('1') == k for B in w)
            print(f"n={n} k={k} c={4*n-7*k} a={a} tau={tau} fano={f} dvecs={st[0]} {time.time()-t0:.0f}s", flush=True)
            done += 1
