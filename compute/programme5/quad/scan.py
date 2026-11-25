"""Scan quadratic level sets L = {B in C(V,k): q(B) = a}: exact tau (up-closure), exact Fano check (d-vectors + SAT),
and, for n >= 11k/6 when Fano-free, a general seven SAT (budgeted).  Usage: py -3.14 scan.py k nmin nmax per_class seed"""
import sys, time, json
import numpy as np
from qlib import *

k, nmin, nmax, per, seed = map(int, sys.argv[1:6])
rng = np.random.default_rng(seed)
BOUND = (3 * k + 5) // 4

def gens(n):
    full = (1 << n) - 1
    for _ in range(per):
        for p in (0.05, 0.15, 0.5):
            yield f'rand{p}', random_graph(n, p, rng), int(rng.integers(0, 1 << n))
        A = int(rng.choice([n // 2, k, n - k + 1]))
        lA = sum(1 << int(x) for x in rng.choice(n, A, replace=False))
        e = int(rng.integers(1, 4))
        ed = [tuple(int(v) for v in rng.choice(n, 2, replace=False)) for _ in range(e)]
        yield f'lin+{e}edges', from_edges(n, ed), lA
        D = [d for d in range(1, n // 2 + 1) if rng.random() < 0.5]
        yield 'circ', circulant(n, D), int(rng.choice([0, full]))
        h = int(rng.integers(1, 3))  # rank 2h: sum of products of indicators of random cells
        cells = rng.integers(0, 2 * h + 1, n)  # cell 2h = "rest"
        ed = []
        for t in range(h):
            X = [x for x in range(n) if cells[x] == 2 * t]; Y = [x for x in range(n) if cells[x] == 2 * t + 1]
            ed += [(x, y) for x in X for y in Y]
        yield f'cells{2*h}', from_edges(n, ed), int(rng.choice([0, full, sum(1 << x for x in range(n) if cells[x] == 0)]))

pc_cache = {}
best = {}
for n in range(nmin, nmax + 1):
    pc = popcount_arr(n)
    c = 4 * n - 7 * k
    for name, G, l in gens(n):
        qv = qtable(n, G, l)
        for a in (0, 1):
            t0 = time.time()
            tau, M = tau_levelset(n, k, qv, a, pc)
            rL = n - k - tau + 1
            rec = dict(n=n, k=k, c=c, cls=name, a=a, q0=int(qv[0]), M=M, tau=tau)
            if tau >= BOUND - 1 and M > 0:
                f, fw, st = fano_exact(n, k, G, l, a, qv, rL, budget=3_000_000)
                if fw: assert check_seven(fw, n)
                rec['fano'] = f
                if f == 'NONE' and 6 * n >= 11 * k:
                    s, sw = seven_sat(n, k, G, l, a, budget=1_000_000)
                    if sw: assert check_seven(sw, n) and all(qv[B] == a and bin(B).count('1') == k for B in sw)
                    rec['any'] = s
                if f == 'NONE':
                    rec['G'] = G; rec['l'] = l
            rec['t'] = round(time.time() - t0, 1)
            print(json.dumps(rec), flush=True)
            key = (n, rec.get('fano', '-'), rec.get('any', '-'))
            best[key] = max(best.get(key, 0), tau)
print('SUMMARY bound', BOUND, json.dumps({str(kk): v for kk, v in sorted(best.items())}), flush=True)
