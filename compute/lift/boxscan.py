"""Steering boxes: after a pair with overlap a, her next request contains the pair intersection and
caps the two new overlaps at c1, c2 with (1-c1) + (1-c2) - a = t (full budget).  The adversary picks
any (x, y) <= (c1, c2) (fresh points lower overlaps).  G(a) = min over c1 of max over the box of W.
[float; W from wval.py]"""
import sys
import numpy as np
from wval import W

def box_max(a, c1, c2, n=7):
    worst = (-1, None)
    for x in np.linspace(0, c1, n):
        for y in np.linspace(0, c2, n):
            if a + x > 1 + 1e-12 or a + y > 1 + 1e-12 or x + y > 1 + 1e-12: continue
            w = W((a, x, y))
            if w > worst[0]: worst = (w, (round(a, 4), round(x, 4), round(y, 4)))
    return worst

if __name__ == '__main__':
    t = eval(sys.argv[1])
    for a in map(eval, sys.argv[2:]):
        tot = 2 - t - a
        best = None
        for c1 in np.linspace(max(0, tot - (1 - a)), tot / 2, 5):
            c2 = tot - c1
            w, at = box_max(a, c1, c2)
            print('  a=%.4f c=(%.4f,%.4f): max W = %.4f at %s' % (a, c1, c2, w, at), flush=True)
            if best is None or w < best[0]: best = (w, c1, c2, at)
        print('a=%.4f  G(a)=%.4f  caps=(%.4f,%.4f)  worst %s  [t=%.4f]' % (a, best[0], best[1], best[2], best[3], t), flush=True)
