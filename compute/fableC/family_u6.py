r"""FABLE_C section 3: family-level Sigma_6 margin for the profile families logged in compute/core12/forced_sevens.jsonl.
Family = union of profile classes C(p), p in family_profiles, for the cell sizes 'cells'.  Exact model (cell level):
six slots with profiles from the family, co-type counts z_{j,A} (A subset of [6], empty allowed) per cell,
u_A = 'type A present', b_A = 'A is disjoint from a present type' (so its points lie in U), minimise |U_6|.
Types are also restricted by the valid fixing 'A present and good  =>  nothing'.  MILP (HiGHS); the optimum's
witness is rebuilt as six explicit co-edges and |U| is recomputed by plain code (upper bound exact; optimality is
solver-certified only).   [computed exact for the witness; computed float/solver for optimality]
Usage: py -3.14 family_u6.py [nproc] [limit]"""
import sys, json, re, os, time, itertools
import numpy as np, scipy.sparse as sp
from scipy.optimize import milp, LinearConstraint, Bounds
from multiprocessing import Pool
here = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(here, '..', 'core12', 'forced_sevens.jsonl')
pc = lambda m: bin(m).count('1')
from classify_sevens import U_of


def min_u6(args):
    k, T, n, cells, fam = args
    q = len(cells); m = len(fam); c = n - k
    nA = 6 * m; nZ = q * 64; nv = nA + nZ + 64 + 64 + nZ
    A_ = lambda i, r: i * m + r; Z_ = lambda j, I: nA + j * 64 + I; U_ = lambda I: nA + nZ + I
    B_ = lambda I: nA + nZ + 64 + I; W_ = lambda j, I: nA + nZ + 128 + j * 64 + I
    ri, ci, vals, lo, hi = [], [], [], [], []
    def add(co, l, h):
        i = len(lo)
        for jj, v in co: ri.append(i); ci.append(jj); vals.append(v)
        lo.append(l); hi.append(h)
    for i in range(6): add([(A_(i, r), 1) for r in range(m)], 1, 1)
    for i in range(5): add([(A_(i, r), r) for r in range(m)] + [(A_(i + 1, r), -r) for r in range(m)], -np.inf, 0)
    for j in range(q):
        add([(Z_(j, I), 1) for I in range(64)], cells[j], cells[j])
        for i in range(6):
            add([(Z_(j, I), 1) for I in range(64) if I >> i & 1] + [(A_(i, r), -fam[r][j]) for r in range(m)], 0, 0)
        for I in range(64):
            add([(Z_(j, I), 1), (U_(I), -cells[j])], -np.inf, 0)
            add([(W_(j, I), 1), (Z_(j, I), -1), (B_(I), -cells[j])], -cells[j], np.inf)   # w >= z - n_j(1-b)
    for I in range(64):
        for J in range(I, 64):
            if I & J == 0:
                add([(B_(I), 1), (U_(I), -1)] + ([(U_(J), -1)] if J != I else []), -1 if J != I else 0, np.inf)
                if J != I: add([(B_(J), 1), (U_(I), -1), (U_(J), -1)], -1, np.inf)
    ub = np.array([1] * nA + [cells[j] for j in range(q) for _ in range(64)] + [1] * 128 +
                  [cells[j] for j in range(q) for _ in range(64)], float)
    cost = np.zeros(nv); cost[nA + nZ + 128:] = 1
    integ = np.ones(nv); integ[nA + nZ + 128:] = 0
    M = sp.csr_matrix((vals, (ri, ci)), shape=(len(lo), nv))
    res = milp(c=cost, constraints=LinearConstraint(M, lo, hi), integrality=integ, bounds=Bounds(np.zeros(nv), ub),
               options={'time_limit': 300})
    if res.x is None: return {'status': int(res.status)}
    x = np.round(res.x).astype(int)
    Ks = [0] * 6; p = 0
    for j in range(q):
        for I in range(64):
            for _ in range(x[Z_(j, I)]):
                for i in range(6):
                    if I >> i & 1: Ks[i] |= 1 << p
                p += 1
    assert p == n and all(pc(K) == c for K in Ks)
    slots = [fam[next(r for r in range(m) if x[A_(i, r)])] for i in range(6)]
    for i in range(6):   # plain re-check that each K_i has its slot profile (so it is a member)
        st = 0
        for j in range(q):
            assert pc(Ks[i] >> st & ((1 << cells[j]) - 1)) == slots[i][j]; st += cells[j]
    u = pc(U_of(Ks, n))
    return {'status': int(res.status), 'minU': u, 'bound': float(res.mip_dual_bound) if hasattr(res, 'mip_dual_bound') else None,
            'slots': slots, 'coedges': Ks}


if __name__ == '__main__':
    npr = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    lim = int(sys.argv[2]) if len(sys.argv) > 2 else None
    fams = {}
    for l in open(SRC, encoding='utf-8'):
        d = json.loads(l); T = int(re.match(r'prof_\w+?_(\d+)_(\d+)_(\d+)_', d['source']).group(2))
        key = (d['k'], T, d['n'], tuple(d['cells']), tuple(sorted(map(tuple, d['family_profiles']))))
        fams[key] = None
    keys = sorted(fams)[:lim]; t0 = time.time()
    print(len(fams), 'distinct families', flush=True)
    with Pool(npr) as p, open(os.path.join(here, 'logs', 'family_u6.jsonl'), 'w', encoding='utf-8') as fo:
        for i, (key, r) in enumerate(zip(keys, p.imap(min_u6, [(k, T, n, list(ce), [list(x) for x in fam]) for k, T, n, ce, fam in keys], chunksize=4))):
            r.update({'k': key[0], 'T': key[1], 'n': key[2], 'cells': list(key[3]), 'family': [list(x) for x in key[4]]})
            fo.write(json.dumps(r) + '\n'); fo.flush()
            if i % 100 == 0: print(i, f'{time.time()-t0:.0f}s', r.get('minU'), r.get('bound'), flush=True)
    print('done', f'{time.time()-t0:.0f}s')
