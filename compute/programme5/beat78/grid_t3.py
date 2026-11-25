"""Tabulate t*_+(x) on the grid x in (Z/G)^3, x_i + x_j <= 1, using tstar.py (all 715 types).
t*_+ treats a zero pairwise part as infinitesimally positive (the adversary may always put o(k) points there;
in every move of the game below a pairwise part can never be forced to be exactly empty, since h_i >= 1-t > 0).
usage: py -3.14 grid_t3.py G NPROC  -> logs/t3_G.npy  (array T[a,b,c], NaN where infeasible)"""
import sys, os, numpy as np
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))

def work(chunk):
    import tstar
    return tstar.tstar_many(chunk)

if __name__ == '__main__':
    G, P = int(sys.argv[1]), int(sys.argv[2])
    pts = [(a, b, c) for a in range(G + 1) for b in range(a, G + 1) for c in range(b, G + 1) if b + c <= G]
    X = np.array(pts, float) / G
    chunks = np.array_split(X, 6 * P)
    with Pool(P) as p: vals = np.concatenate(p.map(work, chunks))
    T = np.full((G + 1,) * 3, np.nan)
    import itertools
    for (a, b, c), v in zip(pts, vals):
        for q in set(itertools.permutations((a, b, c))): T[q] = v
    np.save(os.path.join(HERE, 'logs', 't3_%d.npy' % G), T)
    print('points', len(pts), 'max', np.nanmax(T), 'min', np.nanmin(T))
