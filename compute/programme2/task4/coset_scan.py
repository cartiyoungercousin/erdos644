r"""For each family (n <= 22): the largest fraction of H lying in a coset a' + C(H') that is a majority side of ONE functional u
(top-N functionals by majority fraction, plus the trivial u: whole H) with rho(H') > max(4T-3k, 0).
This is the quantity in the inverse statement 'most members lie in one coset with rho > 4T-3k'.
Output: out/coset_scan.jsonl.   Usage: py -3.14 coset_scan.py [part]   part in 0,1 (splits the inventory)"""
import sys, os, json, glob, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'task1'))
import numpy as np
import families as F
from gf2 import *
from measure import cosetinfo
from tau_star import min_transversal_size
C = F.ROOT
def inventory():
    for m in (2, 3): yield 'fkw', F.fkw(m)[0], None
    yield 'h1', F.h1()[0], None
    for p in sorted(glob.glob(os.path.join(C, 'task3/out/*.npy'))): yield 'task3', F.npy(p, 'task3 ' + os.path.basename(p))[0], None
    yield 'k8', F.coedge_text(os.path.join(C, 'core9/logs/fam_8_6_15_rev.txt'), 15, 'core9 fam_8_6_15_rev')[0], None
    for s in ('pool', 'randdump_s1', 'sevenfree'): yield 'k8', F.coedge_text(os.path.join(C, f'entropy/logs/fam_8_6_15_{s}.txt'), 15, f'entropy fam_8_6_15_{s}')[0], None
    for (k, T, n) in ((8, 6, 15), (8, 6, 16)): yield 'k8', F.coedge_masks(os.path.join(C, f'core12/logs/tgw_fam_{k}_{T}_{n}.txt'), n, f'tgw_fam_{k}_{T}_{n}')[0], None
    for s in ('', '_rand2s1', '_rand2s2', '_rand3s1', '_rand3s2'): yield 'k10', F.coedge_masks(os.path.join(C, f'core12/logs/tgw_fam_10_8_21{s}.txt'), 21, f'tgw_fam_10_8_21{s}')[0], None
    kinds = [("hash", 2), ("hash", 8), ("linear", 2), ("linear", 8), ("parity", 2), ("parity", 8), ("early", 2), ("early", 4),
             ("late", 2), ("late", 4), ("early^hash", 2), ("early^hash", 4), ("junta+", None), ("midhash", 2), ("midhash", 4)]
    for (k, T, n) in ((8, 6, 15), (8, 6, 16)):
        for kind, R in kinds:
            for mode in ('rand', 'rev'):
                if mode == 'rev' and (R or 4) < 2: continue
                try: yield 'hash', F.hash_family(kind, R, mode, n, k, T, seed=1)[0], None
                except Exception: pass
    for r in range(4):
        for sub in itertools.combinations([(9, 2), (10, 1), (11, 0)], r): yield 'nearpool', F.profile_family([(8, 3)] + list(sub))[0], None
def scan(fam, topN=25):
    M = fam.masks; n = fam.n; N = len(M); tau = min_transversal_size(fam); T = tau - 1
    sizes = pc(M); k = int(np.argmax(np.bincount(sizes))); bound = max(4 * T - 3 * k, 0)
    d, rho, _ = cosetinfo(M, n); best = (1.0 if rho > bound else 0.0, None, rho)
    f = np.zeros(1 << n, np.int32); f[M] = 1; hat = fwht(f); n1 = (N - hat) // 2
    frac = np.maximum(n1, N - n1) / N; frac[0] = 0; frac[(n1 == 0) | (n1 == N)] = 0
    for u in np.argsort(-frac)[:topN]:
        u = int(u)
        if frac[u] <= best[0]: break
        par = pc(M & u) & 1; maj = int(par.sum() * 2 > N); sub = M[par == maj]
        d2, rho2, _ = cosetinfo(sub, n)
        if rho2 > bound and len(sub) / N > best[0]: best = (len(sub) / N, [x for x in range(n) if (u >> x) & 1], rho2)
    return dict(name=fam.name, n=n, members=N, k=k, T=T, bound=bound, rho_whole=rho, best_kept_with_rho_gt_bound=round(best[0], 5), u=best[1], rho_sub=best[2], topN=topN)
if __name__ == '__main__':
    part = int(sys.argv[1]) if len(sys.argv) > 1 else None
    for i, (g, fam, _) in enumerate(inventory()):
        if part is not None and i % 2 != part: continue
        r = scan(fam); r['group'] = g; print(json.dumps(r), flush=True); open(os.path.join(HERE, 'out', 'coset_scan.jsonl'), 'a').write(json.dumps(r) + '\n')
