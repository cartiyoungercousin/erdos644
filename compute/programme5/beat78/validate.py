"""Cross-check tstar.py (finite min-max) against the independent MILP of bulk/pencil_cover.py on random shapes."""
import sys, os, random, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'bulk'))
import tstar
from pencil_cover import tstar as milp_tstar
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 200
for x in [(0, .5, .5), (.5, .5, .5), (1/3, 1/3, 1/3), (0, 0, .5), (0, 0, 0), (0, .25, .75), (.1, .2, .7)]:
    print(x, 'minmax %.6f' % tstar.tstar(x), 'milp %.6f' % milp_tstar(x))
bad = 0
for _ in range(N):
    while True:
        x = [rng.random() for _ in range(3)]
        if rng.random() < .3: x[rng.randrange(3)] = 0
        if all(x[i] + x[j] <= 1 for i in range(3) for j in range(i)): break
    a, b = tstar.tstar(x), milp_tstar(x)
    if abs(a - b) > 1e-6: bad += 1; print('MISMATCH', x, a, b)
print('random checks', N, 'mismatches', bad)
