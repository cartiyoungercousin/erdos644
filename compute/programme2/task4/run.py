r"""Run Task 4 measurements over the stored families (same inventory as task1/run_all.py plus controls).
Usage: py -3.14 run.py group [group ...]   groups: fkw ctrl h1 task3 k8 hash nearpool complete sel
Appends one JSON line per family to out/measure.jsonl."""
import sys, os, json, glob, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'task1'))
import numpy as np
import families as F, measure as Mz
from tau_star import Family, popcount
C = F.ROOT; OUT = os.path.join(HERE, 'out', 'measure.jsonl')
def rec(group, fam, **kw):
    r = Mz.measure(fam, **kw); r['group'] = group
    print(json.dumps(r), flush=True); open(OUT, 'a').write(json.dumps(r) + '\n')
def fkw_general(m, n):
    k, nx = 4 * m, 4 * m; a = np.arange(1 << n, dtype=np.int64); pc_ = popcount(a); px = popcount(a & ((1 << nx) - 1))
    return Family(n, a[(pc_ == k) & (px % 2 == 1)], f'FKW m={m} (n={n},k={k})')
def main(groups):
    if 'fkw' in groups:
        for m in (2, 3): rec('fkw', F.fkw(m)[0])
    if 'ctrl' in groups:   # n = 7m+2: Corollary 7 says a Fano-type good seven exists
        rec('ctrl', fkw_general(2, 16)); rec('ctrl', fkw_general(3, 23), fano=True)
    if 'h1' in groups: rec('h1', F.h1()[0])
    if 'task3' in groups:
        for p in sorted(glob.glob(os.path.join(C, 'task3/out/*.npy'))): rec('task3', F.npy(p, 'task3 ' + os.path.basename(p))[0])
    if 'u1' in groups:   # n = 34: tau = 10 taken from Task 1's results.jsonl (ILP at n = 34 timed out here)
        for p in ('gprime_fkw1.npy', 'h1min_random_1.npy'): rec('task3', F.u1(os.path.join(C, 'task3/out', p), 'U1 = pad(' + p + ')')[0], chain=False, tau=10)
    if 'k8' in groups:
        rec('k8', F.coedge_text(os.path.join(C, 'core9/logs/fam_8_6_15_rev.txt'), 15, 'core9 fam_8_6_15_rev')[0])
        for s in ('pool', 'randdump_s1', 'sevenfree'):
            rec('k8', F.coedge_text(os.path.join(C, f'entropy/logs/fam_8_6_15_{s}.txt'), 15, f'entropy fam_8_6_15_{s}')[0])
        for (k, T, n) in ((8, 6, 15), (8, 6, 16)): rec('k8', F.coedge_masks(os.path.join(C, f'core12/logs/tgw_fam_{k}_{T}_{n}.txt'), n, f'tgw_fam_{k}_{T}_{n}')[0])
        for s in ('', '_rand2s1', '_rand2s2', '_rand3s1', '_rand3s2'):
            rec('k10', F.coedge_masks(os.path.join(C, f'core12/logs/tgw_fam_10_8_21{s}.txt'), 21, f'tgw_fam_10_8_21{s}')[0])
        rec('k13', F.coedge_masks(os.path.join(C, 'core12/logs/tgw_fam_13_10_25.txt'), 25, 'tgw_fam_13_10_25')[0], chain=False)
    if 'hash' in groups:
        kinds = [("hash", 2), ("hash", 8), ("linear", 2), ("linear", 8), ("parity", 2), ("parity", 8), ("early", 2), ("early", 4),
                 ("late", 2), ("late", 4), ("early^hash", 2), ("early^hash", 4), ("junta+", None), ("midhash", 2), ("midhash", 4)]
        for (k, T, n) in ((8, 6, 15), (8, 6, 16)):
            for kind, R in kinds:
                for mode in ('rand', 'rev'):
                    if mode == 'rev' and (R or 4) < 2: continue
                    try: fam, _ = F.hash_family(kind, R, mode, n, k, T, seed=1)
                    except Exception as e: print('skip', kind, R, mode, repr(e)); continue
                    rec('hash', fam)
    if 'nearpool' in groups:
        for r in range(4):
            for sub in itertools.combinations([(9, 2), (10, 1), (11, 0)], r):
                rec('nearpool', F.profile_family([(8, 3)] + list(sub))[0])
    if 'complete' in groups:
        for k in (5, 9, 13):
            n = -(-7 * k // 4); rec('complete', F.complete(n, k)[0], chain=(n <= 22))
if __name__ == '__main__': main(sys.argv[1:])
