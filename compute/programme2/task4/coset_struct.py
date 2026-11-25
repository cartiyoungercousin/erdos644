r"""Cheap structural pass over the same inventory as run.py: annihilator of C(H) (the parity checks defining the smallest
coset a + C(H) containing H), and an EXACT count of triples x1+x2 = x3 (zero-weight triple sums = perfect pencils) for
families with <= 5000 members.  Appends to out/struct.jsonl.  Usage: py -3.14 coset_struct.py"""
import sys, os, json, glob, itertools
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'task1'))
import numpy as np
import families as F
from gf2 import *
C = F.ROOT
def struct(fam):
    M = fam.masks; n = fam.n; B = reduced_basis(M ^ M[0], n); H = annihilator(B, n); full = (1 << n) - 1
    ann = [[x for x in range(n) if (h >> x) & 1] for h in H]
    # which annihilator elements are the all-ones functional (parity of size) -- trivial for uniform families
    d = dict(name=fam.name, n=n, members=len(M), codim=len(H), ann_supports=[a if len(a) <= n // 2 else ['complement of', [x for x in range(n) if x not in a]] for a in ann][:6],
             ann_parity_of_a=[bin(h & int(M[0])).count('1') & 1 for h in H][:6])
    if len(M) <= 5000:
        S = set(int(m) for m in M); cnt = 0; Ml = [int(m) for m in M]
        for i in range(len(Ml)):
            t = M[i] ^ M[i + 1:]; cnt += int(np.isin(t, M).sum())
        d['triples_x1+x2=x3'] = cnt // 3
    return d
def emit(fam):
    d = struct(fam); print(json.dumps(d), flush=True); open(os.path.join(HERE, 'out', 'struct.jsonl'), 'a').write(json.dumps(d) + '\n')
if __name__ == '__main__':
    import numpy as np
    for m in (2, 3): emit(F.fkw(m)[0])
    emit(F.h1()[0])
    for p in sorted(glob.glob(os.path.join(C, 'task3/out/*.npy'))): emit(F.npy(p, 'task3 ' + os.path.basename(p))[0])
    for p in ('gprime_fkw1.npy', 'h1min_random_1.npy'): emit(F.u1(os.path.join(C, 'task3/out', p), 'U1 = pad(' + p + ')')[0])
    emit(F.coedge_text(os.path.join(C, 'core9/logs/fam_8_6_15_rev.txt'), 15, 'core9 fam_8_6_15_rev')[0])
    for s in ('pool', 'randdump_s1', 'sevenfree'): emit(F.coedge_text(os.path.join(C, f'entropy/logs/fam_8_6_15_{s}.txt'), 15, f'entropy fam_8_6_15_{s}')[0])
    for (k, T, n) in ((8, 6, 15), (8, 6, 16)): emit(F.coedge_masks(os.path.join(C, f'core12/logs/tgw_fam_{k}_{T}_{n}.txt'), n, f'tgw_fam_{k}_{T}_{n}')[0])
    for s in ('', '_rand2s1', '_rand2s2', '_rand3s1', '_rand3s2'): emit(F.coedge_masks(os.path.join(C, f'core12/logs/tgw_fam_10_8_21{s}.txt'), 21, f'tgw_fam_10_8_21{s}')[0])
    emit(F.coedge_masks(os.path.join(C, 'core12/logs/tgw_fam_13_10_25.txt'), 25, 'tgw_fam_13_10_25')[0])
    for k in (5, 9, 13):
        n = -(-7 * k // 4); emit(F.complete(n, k)[0])
