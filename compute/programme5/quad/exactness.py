"""Exactness lemma check: at 4n = 7k, {q = 1} with q(0) = 0 has no Fano seven; {q = 0} usually has one."""
import numpy as np, time
from qlib import *
rng = np.random.default_rng(3)
for (n, k) in [(7, 4)]:
    for s in range(4):
        G = random_graph(n, 0.5, rng); l = int(rng.integers(0, 1 << n)); qv = qtable(n, G, l)
        for a in (1, 0):
            t0 = time.time(); tau, M = tau_levelset(n, k, qv, a)
            f, w, st = fano_exact(n, k, G, l, a, qv, n - k - tau + 1, budget=5_000_000)
            print(f"n={n} k={k} seed{s} a={a} |L|={M} tau={tau} fano={f} {time.time()-t0:.1f}s", flush=True)
