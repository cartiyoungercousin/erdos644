"""Window part (p > t, i.e. N < 3 - t) of a steering box {(a, x, y): x <= c1, y <= c2}: max of W.
usage: py winscan.py t a c1 c2 [n]   [float]"""
import sys
import numpy as np
from wval import W
t, a, c1, c2 = (eval(s) for s in sys.argv[1:5])
n = int(sys.argv[5]) if len(sys.argv) > 5 else 9
bad = []
worst = (-1, None)
for x in np.linspace(0, c1, n):
    for y in np.linspace(0, c2, n):
        if a + x + y <= t + 1e-12 or a + x > 1 or a + y > 1 or x + y > 1: continue
        b, v = W((a, x, y), True)
        if b > worst[0]: worst = (b, (a, x, y), v)
        if b > t + 1e-9: bad.append(((round(a, 3), round(x, 3), round(y, 3)), round(b, 4)))
print('t=%.4f a=%.4f caps=(%.4f,%.4f): window max W = %.4f at %s %s' % (t, a, c1, c2, worst[0], tuple(round(z, 4) for z in worst[1]) if worst[1] else None, {k: round(float(q), 4) for k, q in worst[2].items()} if worst[1] else ''))
print('  failing window shapes:', len(bad), bad[:12])
