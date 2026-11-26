"""Independent check of a stage1g INFEASIBLE certificate (logs/stage1g_<tag>.json).   No code shared with
cover.py / stage1g.py.  (1) Coverage of every plan on its support: all alive atom pairs of the frame among the
plan's atoms (possible atoms minus the ones it requires empty) have pairwise-intersecting used vectors, atoms fully
placed.  (2) Adversary side: on a 0.25-grid (plus caps) and on random continuous M1, every S*-legal M1 avoiding R1
has a plan that applies (its required-empty atoms are empty) and whose largest request is <= t."""
import json, sys, itertools
import numpy as np

MEMB = {'X': 'EF', 'Y': 'EG', 'Z': 'FG', 'A': 'GK', 'Gd': 'G', 'B': 'FK', 'Fd': 'F', 'EpK': 'EK', 'Ep': 'E', 'OK': 'K'}
FR = {'FGKM1': 'FGKM', 'EGKM1': 'EGKM', 'EFKM1': 'EFKM', 'EFGM1': 'EFGM', 'EFGKM1': 'EFGKM'}
SPEC = [(0.0, 45 / 12), (5.0, 73 / 12), (80 / 12, 14.0)]
ZH = 1e-3 / 2


def parse(k):
    c, b = k.split('|'); return (c, int(b))


def main(fn, step=0.25, nrand=20):
    d = json.load(open(fn)); S = d['S']; r1 = d['R1']; t = d['t']
    cells = [c for c in MEMB if c != 'Z']
    possible = [(c, 1) for c in cells if S[c] - r1.get(c, 0) > 1e-9] + [(c, 0) for c in cells if S[c] > 1e-9] + [('Z', 0), ('Z', 1)]
    inm = lambda a, m: (a[1] == 1) if m == 'M' else (m in MEMB[a[0]])
    plans = []; bad = 0
    for entry in d['plans']:
        nm, vec = entry[0], entry[1]; need = entry[2] if len(entry) > 2 else []
        vec = {parse(k): v for k, v in vec.items()}; need = [parse(k) for k in need]
        sup = [a for a in possible if a not in need]
        al = [(p, q) for p, q in itertools.combinations_with_replacement(sup, 2) if all(inm(p, m) or inm(q, m) for m in FR[nm])]
        for a in set(x for pq in al for x in pq):
            if a not in vec or abs(sum(f for _, f in vec[a]) - 1) > 1e-6: bad += 1
        for p, q in al:
            for v, f in vec.get(p, []):
                for w, g in vec.get(q, []):
                    if f > 1e-12 and g > 1e-12 and not any(x and y for x, y in zip(v, w)): bad += 1
        r = len(next(iter(vec.values()))[0][0])
        plans.append(({a: [sum(f for v, f in lst if v[i]) for i in range(r)] for a, lst in vec.items()}, need, r))
    print(fn, ': plans', len(plans), 'coverage violations', bad)
    cap = np.array([max(0.0, S[c] - r1.get(c, 0)) for c in cells])

    def evalM(M):
        sz = {}
        for j, c in enumerate(cells): sz[(c, 1)] = M[:, j]; sz[(c, 0)] = S[c] - M[:, j]
        sz[('Z', 0)] = sz[('Z', 1)] = np.full(len(M), ZH)
        best = np.full(len(M), np.inf)
        for coef, need, r in plans:
            L = np.max([sum(coef[a][i] * sz[a] for a in coef) for i in range(r)], axis=0)
            ok = np.ones(len(M), bool)
            for a in need: ok &= sz[a] <= 1e-12
            best = np.minimum(best, np.where(ok, L, np.inf))
        return best

    def legal(M):
        ok = M.sum(1) <= 14 + 1e-9
        for P in 'EFGK':
            T_ = sum(M[:, j] for j, c in enumerate(cells) if P in MEMB[c])
            ok &= np.any([(T_ >= lo - 1e-9) & (T_ <= hi + 1e-9) for lo, hi in SPEC], axis=0)
        return ok
    grids = [sorted(set([round(x, 6) for x in np.arange(0, cap[j] + 1e-9, step)] + [round(cap[j], 6)])) for j in range(len(cells))]
    G = np.array(list(itertools.product(*grids)), float); G = G[legal(G)]
    wg = (evalM(G) - t).max() if len(G) else -np.inf
    print('  grid M1 (legal):', len(G), ' max(best plan - t) = %.6f' % wg)
    rng = np.random.default_rng(1); wr = -np.inf
    for _ in range(nrand):
        M = rng.random((100000, len(cells))) * cap
        M = np.where(rng.random(M.shape) < 0.25, cap, M); M = np.where(rng.random(M.shape) < 0.25, 0.0, M)
        M = M[legal(M)]
        if len(M): wr = max(wr, (evalM(M) - t).max())
    print('  random M1: max(best plan - t) = %.6f' % wr)
    print('  VERDICT', 'OK' if bad == 0 and wg <= 1e-9 and wr <= 1e-9 else 'FAIL')


if __name__ == '__main__':
    main(sys.argv[1], float(sys.argv[2]) if len(sys.argv) > 2 else 0.25)
