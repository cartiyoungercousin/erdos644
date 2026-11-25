r"""Counting picture (notes section 5), checked by sampling: fraction of uniformly random labellings
V'' -> F2^3 - 0 with fixed region sizes m (7 regions) whose three bit-classes are codewords, against the main term
8 / |D|^3 (D = row space of the column matrix, which contains the all-ones word).  Structures: random columns,
q planted series pairs (dual words of weight 2), one coloop (dual word of weight 1), small cells.
Sampling, so [computed, Monte Carlo]; the series prediction (8/7)^q is the exact product formula for independent pairs."""
import random, sys, json, os
import numpy as np
sys.path.insert(0, os.path.dirname(__file__))
from b1 import rank

def run(kind, m=6, M=3, q=0, samples=400000, seed=0):
    rng = random.Random(seed); N = 7 * m
    cols = [rng.getrandbits(M) for _ in range(N)]
    R = M
    if kind == 'series':
        for t in range(q):
            x, y = 2 * t, 2 * t + 1
            cols[x] |= 1 << (R + t); cols[y] |= 1 << (R + t)
        R += q
    if kind == 'coloop':
        cols[0] |= 1 << R; R += 1
    if kind == 'cells':          # columns from a pool of q values (cells of size about N/q)
        pool = [rng.getrandbits(M) for _ in range(q)]; cols = [rng.choice(pool) for _ in range(N)]
    cols = [c | (1 << R) for c in cols]          # parity row: even code, all-ones in D
    rD = rank(cols)
    main = 8.0 / 2 ** (3 * rD)
    labels = np.repeat(np.arange(1, 8), m)
    C = np.array(cols, dtype=np.int64)
    nprng = np.random.default_rng(seed)
    hits = 0; B = 20000
    for _ in range(samples // B):
        L = np.array([nprng.permutation(labels) for _ in range(B)])
        ok = np.ones(B, dtype=bool)
        for i in range(3):
            sel = (L >> i) & 1
            s = np.bitwise_xor.reduce(np.where(sel == 1, C[None, :], 0), axis=1)
            ok &= (s == 0)
        hits += ok.sum()
    f = hits / samples
    return dict(kind=kind, m=m, M=M, q=q, rankD=rD, main=main, freq=f, ratio=f / main if main else None)

if __name__ == '__main__':
    out = open(os.path.join(os.path.dirname(__file__), 'logs', 'montecarlo.jsonl'), 'w')
    for args in [('rand', 6, 3, 0), ('rand', 6, 4, 0), ('series', 6, 2, 1), ('series', 6, 2, 2), ('series', 6, 1, 3),
                 ('coloop', 6, 3, 0), ('cells', 6, 4, 3)]:
        r = run(*args); print(r, flush=True); out.write(json.dumps({k: (float(v) if isinstance(v, (np.floating, np.integer)) else v) for k, v in r.items()}) + '\n')
