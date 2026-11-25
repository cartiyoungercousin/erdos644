"""Two-request three-anchor game (asymptotic, units of k), over ALL seven-types via pencil_cover.tstar.
x1 any; x2 avoids a T-subset of x1 => d12 = |x1 cap x2| in [0, 1-t] (adversary); x3 avoids S3 = (x1 cap x2)
+ a points of x1-x2 + b points of x2-x1 (a+b <= t-d12; we choose) => triple intersection empty,
d13 in [0, 1-d12-a], d23 in [0, 1-d12-b] (adversary; large n gives room). Finish: static 4-block cover,
t*(d23,d13,d12) <= t. Reports, for each t, the adversary's best (d12, d13, d23) against our best (a, b) on a grid.
usage: py -3.14 game3.py t GRID NPROC"""
import sys, itertools
from multiprocessing import Pool
from pencil_cover import tstar

def val(args):
    t, d12, a, b, G = args
    worst = (0, None)
    m13, m23 = 1 - d12 - a, 1 - d12 - b
    for i in range(G + 1):
        for j in range(G + 1):
            d13, d23 = m13 * i / G, m23 * j / G
            v = tstar((d23, d13, d12))
            if v > worst[0]: worst = (v, (d12, d13, d23))
    return (d12, a, b), worst

if __name__ == '__main__':
    t, G, P = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    q = 1 - t
    jobs = []
    for d12 in [q * u / 3 for u in range(4)]:
        for ua in range(G + 1):
            for ub in range(ua, G + 1):
                a, b = (t - d12) * ua / G, (t - d12) * ub / G
                if a + b <= t - d12 + 1e-12: jobs.append((t, d12, a, b, G))
    with Pool(P) as p: res = p.map(val, jobs)
    best = {}
    for (d12, a, b), w in res:
        if d12 not in best or w[0] < best[d12][0]: best[d12] = (w[0], a, b, w[1])
    print('t=%.4f' % t)
    for d12 in sorted(best): print('  d12=%.4f  our best a,b=(%.3f,%.3f)  adversary value %.4f at %s' % (d12, best[d12][1], best[d12][2], best[d12][0], best[d12][3]))
    print('  game value (max over d12):', max(v[0] for v in best.values()), ' <= t ?', max(v[0] for v in best.values()) <= t + 1e-9)
