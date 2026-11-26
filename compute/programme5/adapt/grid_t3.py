"""Static three-anchor finish t*_+ (all 715 classes; beat78/tstar.py) tabulated on the grid (Z/G)^3.
Same as beat78/grid_t3.py but with small chunks (memory) so G = 168 fits in 6 processes.
usage: py -3.14 grid_t3.py G NPROC  -> logs/t3_G.npy"""
import sys, os, itertools, numpy as np
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'beat78'))

def work(X):
    import tstar
    T = tstar.tab(); out = np.empty(len(X))
    M = np.stack([X[:, 0], X[:, 1], X[:, 2], 1 - X[:, 1] - X[:, 2], 1 - X[:, 0] - X[:, 2], 1 - X[:, 0] - X[:, 1]], 1)
    for s in range(0, len(X), 24):
        V = np.einsum('clr,nr->ncl', T['K'], M[s:s + 24])
        out[s:s + 24] = V.max(axis=2).min(axis=1)
    return out

if __name__ == '__main__':
    G, P = int(sys.argv[1]), int(sys.argv[2])
    pts = [(a, b, c) for a in range(G + 1) for b in range(a, G + 1) for c in range(b, G + 1) if b + c <= G]
    X = np.array(pts, float) / G
    chunks = np.array_split(X, 40 * P)
    with Pool(P) as p: vals = np.concatenate(p.map(work, chunks))
    T = np.full((G + 1,) * 3, np.nan)
    for (a, b, c), v in zip(pts, vals):
        for q in set(itertools.permutations((a, b, c))): T[q] = v
    np.save(os.path.join(HERE, 'logs', 't3_%d.npy' % G), T)
    print('points', len(pts), 'max', np.nanmax(T), 'min', np.nanmin(T))
