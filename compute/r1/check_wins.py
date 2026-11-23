"""Independent sanity check of requester wins (no MILP): for every 'adaptive' record of a grid
file, sample many admissible responses K (random points and random greedy extreme points of the
response polytope) and verify that some pattern of the recorded pool closes with all loads <= t.

usage: py check_wins.py out/grid_VARIANT_T_....jsonl VARIANT T [nsamples=20000]
"""
import sys, json
from fractions import Fraction
import numpy as np
import game

def main(fn, variant, tstr, ns=20000):
    t = float(Fraction(tstr)); pden = int(fn.replace("\\", "/").split("_")[-2])
    rng = np.random.default_rng(0); nprof = 0; worst = -1.0; bad = 0
    for line in open(fn):
        r = json.loads(line)
        if r.get("win") != "adaptive": continue
        i, j, l = r["p"]; x, y, z = i / pden, j / pden, l / pden
        mass = game.cell_mass(x, y, z); d = r["D"]; rules = game.make_rules(variant, t, x, y, z)
        cls = {C.name: C for C in game.closures(mass, d)}
        rows = [cls[name].W[idx] @ cls[name].M for name, idx in r["pool"]]      # each [nLam, 13]
        cap = np.array([max(mass[c] - d[c], 0.0) for c in range(6)])
        K = []
        while len(K) < ns:
            mode = rng.integers(3)
            if mode == 0: kv = cap * rng.random(6)
            elif mode == 1: kv = cap * (rng.random(6) < rng.random())
            else:
                kv = np.zeros(6); rem = 1.0
                for c in rng.permutation(6):
                    a = min(cap[c], rem) * (rng.random() < 0.8); kv[c] = a; rem -= a
            if kv.sum() > 1: kv = kv / kv.sum()
            kv = list(kv) + [1 - kv.sum()]
            if game.admissible(mass, d, kv, rules): K.append(kv)
        K = np.array(K)
        RM = np.zeros((len(K), 13))
        for c in range(6): RM[:, 2 * c] = K[:, c]; RM[:, 2 * c + 1] = mass[c] - K[:, c]
        RM[:, 12] = K[:, 6]
        best = np.full(len(K), 9.0)
        for R in rows: best = np.minimum(best, (RM @ R.T).max(axis=1))
        nprof += 1; worst = max(worst, best.max() - t); bad += int((best > t + 1e-6).sum())
    print(f"{fn}: {nprof} adaptive wins, {ns} sampled responses each; responses not closed by the pool: {bad}; "
          f"max (load - t) over all samples: {worst:+.2e}")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 20000)
