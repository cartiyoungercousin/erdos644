"""Per-class static three-anchor lemma values at the obstruction profile {c, 0+, 0+} (independent code path:
bulk/anchor3_lp.py LP over the co-types of each of the 715 maximal intersecting classes, all labellings).
Pairwise parts x cap w, x' cap w get mass 1e-9 (nonempty).  Reports min over labellings per class, and the
minimum within the Fano class, class 195 (HUB), the four LP-11/6 classes and all LP-15/8 classes.
usage: py -3.14 classes_at.py NPROC -> logs/classes_at.log"""
import sys, os, itertools
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'bulk'))
import anchor3_lp as A
CS = [0.5, 17 / 32, 5 / 9, 9 / 16, 0.6]
TINY = 1e-9
def prof(c): return dict(Dab=c, Dac=TINY, Dbc=TINY, Ea=1 - c - TINY, Eb=1 - c - TINY, Ec=1 - 2 * TINY)
def job(ci):
    i, lp, fano, M = A.CLS[ci]; Ms = set(M)
    best = [9.0] * len(CS)
    for F in itertools.permutations(range(7), 3):
        if sum(1 << x for x in F) not in Ms: continue
        for s, c in enumerate(CS):
            v = A.solve(M, F, prof(c))
            if v is not None and v < best[s]: best[s] = v
    return i, lp, fano, best
if __name__ == '__main__':
    with Pool(int(sys.argv[1])) as p: res = p.map(job, range(len(A.CLS)))
    out = open(os.path.join(HERE, 'logs', 'classes_at.log'), 'w')
    def P(*a): print(*a); print(*a, file=out, flush=True)
    P('c values:', CS, ' target (c+3)/4:', [round((c + 3) / 4, 5) for c in CS])
    groups = {'Fano': [r for r in res if r[2]], 'class195': [r for r in res if r[0] == 195],
              'LP-11/6': [r for r in res if r[1] == '11/6'], 'LP-15/8': [r for r in res if r[1] == '15/8'],
              'all': res}
    for g, rs in groups.items():
        mins = [min(r[3][s] for r in rs) for s in range(len(CS))]
        arg = [min(rs, key=lambda r: r[3][s])[0] for s in range(len(CS))]
        P('%-8s (%3d classes) min value per c: %s  attained by class %s' % (g, len(rs), [round(m, 5) for m in mins], arg))
    for r in groups['LP-11/6']: P('  11/6 class %d: %s' % (r[0], [round(v, 5) for v in r[3]]))
    out.close()
