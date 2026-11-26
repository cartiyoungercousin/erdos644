"""Independent check of a stage-1 INFEASIBLE certificate (logs/stage1_<tag>.json).  [computed exact on plans;
sampled + grid check of the adversary side]   No code shared with cover.py / frames.py / stage1.py.
(1) Coverage: for every plan, every alive atom pair of its frame (atoms = base cell x in/out of M1, restricted to
    atoms that can be nonempty for this R1) has all its used membership vectors pairwise intersecting, and every
    such atom is fully placed (fractions sum to 1).
(2) Adversary side: on a 0.25-grid of M1 (plus Y/B remnants at their caps) and on random continuous M1, every
    S*-legal M1 avoiding R1 has some plan whose largest request is <= t."""
import json, sys, itertools, random
import numpy as np

CELLS = ['X', 'Y', 'A', 'B', 'Ep', 'Fd', 'Gd']
MEM = {'X': 'EF', 'Y': 'EG', 'A': 'GK', 'B': 'FK', 'Ep': 'E', 'Fd': 'F', 'Gd': 'G', 'Z': 'FG'}
FR = {'FGKM1': 'FGKM', 'EGKM1': 'EGKM', 'EFKM1': 'EFKM', 'EFGM1': 'EFGM', 'EFGKM1': 'EFGKM'}
SPEC = [(0.0, 45 / 12), (5.0, 73 / 12), (80 / 12, 14.0)]
TR = {'E': ['X', 'Y', 'Ep'], 'F': ['X', 'B', 'Fd'], 'G': ['Y', 'A', 'Gd'], 'K': ['A', 'B']}
import os
AL = float(os.environ.get('ALPHA', '7.0'))
SIZE = {'X': 6, 'Y': 5, 'A': AL, 'B': 14 - AL, 'Ep': 3, 'Fd': AL - 6, 'Gd': 9 - AL}
ZE = 1e-3 / 2


def inmem(atom, mem):
    c, b = atom
    if mem == 'M': return b == 1
    return mem in MEM[c]


def main(fn):
    d = json.load(open(fn)); r1 = d['R1']; t = d['t']
    possible = [(c, 1) for c in CELLS if SIZE[c] - r1[c] > 1e-9] + [(c, 0) for c in CELLS] + [('Z', 0), ('Z', 1)]
    plans = []
    bad = 0
    for nm, phi, vec in d['plans']:
        vec = {tuple([k.split('|')[0], int(k.split('|')[1])]): v for k, v in vec.items()}
        fr = FR[nm]
        al = [(p, q) for p, q in itertools.combinations_with_replacement(possible, 2)
              if all(inmem(p, m) or inmem(q, m) for m in fr)]
        used = set(x for pq in al for x in pq)
        for a in used:
            if a not in vec or abs(sum(f for _, f in vec[a]) - 1) > 1e-6: bad += 1
        for p, q in al:
            for v, f in vec.get(p, []):
                for w, g in vec.get(q, []):
                    if f > 1e-12 and g > 1e-12 and not any(x and y for x, y in zip(v, w)): bad += 1
        r = len(next(iter(vec.values()))[0][0])
        coef = {}
        for a, lst in vec.items():
            coef[a] = [sum(f for v, f in lst if v[i]) for i in range(r)]
        plans.append(coef)
    print('plans', len(plans), 'coverage violations', bad)

    def sizes_of(M):     # M: array (N, 7) masses in M1 per cell
        out = {}
        for j, c in enumerate(CELLS):
            out[(c, 1)] = M[:, j]; out[(c, 0)] = SIZE[c] - M[:, j]
        out[('Z', 0)] = np.full(len(M), ZE); out[('Z', 1)] = np.full(len(M), ZE)
        return out

    def legal(M):
        ok = (M.sum(1) <= 14 + 1e-9)
        for P, cs in TR.items():
            T_ = sum(M[:, CELLS.index(c)] for c in cs)
            ok &= np.any([(T_ >= lo - 1e-9) & (T_ <= hi + 1e-9) for lo, hi in SPEC], axis=0)
        return ok

    def worst(M):
        sz = sizes_of(M); best = np.full(len(M), np.inf)
        for coef in plans:
            r = len(next(iter(coef.values())))
            L = np.max([sum(coef[a][i] * sz[a] for a in coef) for i in range(r)], axis=0)
            best = np.minimum(best, L)
        return best

    cap = np.array([SIZE[c] - r1[c] for c in CELLS])
    grids = [sorted(set([round(x, 6) for x in np.arange(0, cap[j] + 1e-9, 0.25)] + [round(cap[j], 6)])) for j in range(7)]
    G = np.array(list(itertools.product(*grids)), float)
    G = G[legal(G)]
    w = worst(G)
    print('grid points (legal, avoiding R1):', len(G), ' max over them of best plan size - t = %.6f' % (w.max() - t))
    rng = np.random.default_rng(0); worst_all = -np.inf
    for _ in range(20):
        M = rng.random((200000, 7)) * cap
        M = np.where(rng.random(M.shape) < 0.25, cap, M)
        M = np.where(rng.random(M.shape) < 0.15, 0.0, M)
        M = M[legal(M)]
        if len(M): worst_all = max(worst_all, (worst(M) - t).max())
    print('random continuous M1: max of best plan size - t = %.6f' % worst_all)
    print('VERDICT', 'OK' if bad == 0 and w.max() <= t + 1e-9 and worst_all <= 1e-9 else 'FAIL')


if __name__ == '__main__':
    main(sys.argv[1])
