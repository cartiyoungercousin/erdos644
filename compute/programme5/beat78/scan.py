"""Value of the pair-tree game (pairgame.solve) on a nu grid, by bisection in t (t continuous, responses on the
1/G grid).  Output: largest t where the adversary still wins, eps = t - 3/4.  usage: py -3.14 scan.py G"""
import sys, os, numpy as np
from pairgame import load, solve
G = int(sys.argv[1]); T3 = load(G)
HERE = os.path.dirname(os.path.abspath(__file__))
out = open(os.path.join(HERE, 'logs', 'scan_%d.log' % G), 'w')
for nu in [2.0, 2.1, 2.2, 53/24, 2.25, 2.3, 2.35, 2.4, 2.45, 2.5, 2.55, 2.6, 2.65, 2.7, 2.75, 2.8, 2.85, 2.875, 2.9, 3.0, 3.5, 4.0, 10.0, 1000.0]:
    lo, hi = 0.75, 1.0
    if not solve(T3, G, nu, lo)[0]: v = None
    else:
        for _ in range(30):
            mid = (lo + hi) / 2
            if solve(T3, G, nu, mid)[0]: lo = mid
            else: hi = mid
        v = lo
    line = 'nu=%.4f  adversary wins up to t=%.5f  eps=%.5f  (eps-1/8 = %+.5f)' % (nu, v, v - .75, v - .875)
    print(line); print(line, file=out, flush=True)
