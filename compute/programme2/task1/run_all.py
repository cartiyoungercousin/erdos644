r"""Run Task 1 over all stored families; append one JSON line per family to out/results.jsonl.  Usage: py -3.14 run_all.py [group ...]
groups: fkw h1 task3 k8 hash nearpool complete"""
import sys, os, json, glob, time, itertools
from tau_star import *; import families as F
HERE = os.path.dirname(os.path.abspath(__file__)); os.makedirs(os.path.join(HERE, 'out'), exist_ok=True)
OUT = os.path.join(HERE, 'out', 'results.jsonl'); C = F.ROOT
def rec(group, fam, orb, sym_only=False, kind=None, also_direct=False):
    t = time.time(); tm = min_transversal_size(fam, kind)
    outs = []
    for o in ([orb] if orb is not None else [None]) + ([None] if (also_direct and orb is not None) else []):
        r = solve(fam, o, kind=kind)
        cond_opt, cond_phi = classify(r)
        d = dict(group=group, name=fam.name, n=fam.n, members=int(len(fam.masks)), tau=tm, tau_b=r['tau_b'], tau_b_frac=frac(r['tau_b']),
                 margin=SEVEN_THIRDS - r['tau_b'], max_atom=r['max_atom'], atom_frac=frac(r['max_atom']), phi=r['phi'],
                 uniform_bound=fam.n / tm, rich=bool(cond_phi), rich_opt_y=bool(cond_opt), symmetric=r['symmetric'], oracle=r['oracle'],
                 cuts=r['cuts'], secs=round(time.time() - t, 1))
        print(json.dumps(d), flush=True); open(OUT, 'a').write(json.dumps(d) + '\n')
def main(groups):
    if 'fkw' in groups:
        for m in (2, 3):
            fam, orb = F.fkw(m); rec('fkw', fam, orb, also_direct=True)
    if 'h1' in groups:
        fam, orb = F.h1(); rec('h1', fam, orb, also_direct=True)
    if 'task3' in groups:
        for p in sorted(glob.glob(os.path.join(C, 'task3/out/*.npy'))):
            fam, orb = F.npy(p, 'task3 ' + os.path.basename(p)); rec('task3', fam, orb)
        for p in ('gprime_fkw1.npy', 'h1min_random_1.npy'):
            fam, orb = F.u1(os.path.join(C, 'task3/out', p), 'U1 = pad(' + p + ')'); rec('task3', fam, orb, kind='ilp')
    if 'k8' in groups:
        fam, orb = F.coedge_text(os.path.join(C, 'core9/logs/fam_8_6_15_rev.txt'), 15, 'core9 fam_8_6_15_rev'); rec('k8', fam, orb)
        for s in ('pool', 'randdump_s1', 'sevenfree'):
            fam, orb = F.coedge_text(os.path.join(C, f'entropy/logs/fam_8_6_15_{s}.txt'), 15, f'entropy fam_8_6_15_{s}'); rec('k8', fam, orb)
        for (k, T, n) in ((8, 6, 15), (8, 6, 16)):
            fam, orb = F.coedge_masks(os.path.join(C, f'core12/logs/tgw_fam_{k}_{T}_{n}.txt'), n, f'tgw_fam_{k}_{T}_{n}'); rec('k8', fam, orb)
        for s in ('', '_rand2s1', '_rand2s2', '_rand3s1', '_rand3s2'):
            fam, orb = F.coedge_masks(os.path.join(C, f'core12/logs/tgw_fam_10_8_21{s}.txt'), 21, f'tgw_fam_10_8_21{s}'); rec('k10', fam, orb)
        fam, orb = F.coedge_masks(os.path.join(C, 'core12/logs/tgw_fam_13_10_25.txt'), 25, 'tgw_fam_13_10_25'); rec('k13', fam, orb)
    if 'hash' in groups:
        kinds = [("hash", 2), ("hash", 8), ("linear", 2), ("linear", 8), ("parity", 2), ("parity", 8), ("early", 2), ("early", 4),
                 ("late", 2), ("late", 4), ("early^hash", 2), ("early^hash", 4), ("junta+", None), ("midhash", 2), ("midhash", 4)]
        for (k, T, n) in ((8, 6, 15), (8, 6, 16)):
            for kind, R in kinds:
                for mode in ('rand', 'rev'):
                    if mode == 'rev' and (R or 4) < 2: continue
                    try: fam, orb = F.hash_family(kind, R, mode, n, k, T, seed=1)
                    except Exception as e: print('skip', kind, R, mode, repr(e)); continue
                    rec('hash', fam, orb)
    if 'nearpool' in groups:
        for r in range(4):
            for sub in itertools.combinations([(9, 2), (10, 1), (11, 0)], r):
                fam, orb = F.profile_family([(8, 3)] + list(sub)); rec('nearpool', fam, orb)
    if 'complete' in groups:
        for k in (5, 9, 13):
            n = -(-7 * k // 4); fam, orb = F.complete(n, k); rec('complete', fam, orb)
if __name__ == '__main__': main(sys.argv[1:] or ['fkw', 'h1', 'task3', 'k8', 'hash', 'nearpool', 'complete'])
