"""Re-run of bulk/game3.py (two-request three-anchor game, large n) with the missing constraint d13 + d23 <= 1
(x3 has k points; game3 allowed |x3 cap x1| = |x3 cap x2| = 9k/16).  Grid 1/G on all coordinates, t*_+ table.
value(t) = max_{d12 in [0,1-t]} min_{a+b <= t-d12} max_{d13<=1-d12-a, d23<=1-d12-b, d13+d23<=1} t*.
usage: py -3.14 game3_fixed.py G t"""
import sys, numpy as np
from pairgame import load
G, t = int(sys.argv[1]), float(sys.argv[2]); T3 = load(G); g = np.arange(G + 1) / G
best = (-1, None)
for j in range(G + 1):
    if g[j] > 1 - t + 1e-12: break
    sub = np.nan_to_num(T3[j], nan=-1.0)
    sub = np.where(g[:, None] + g[None, :] <= 1 + 1e-12, sub, -1.0)
    M = np.maximum.accumulate(np.maximum.accumulate(sub, 0), 1)     # max t* over the box [0,h1]x[0,h2]
    req = (9, None)
    for a in range(G + 1):
        for b in range(G + 1):
            if g[a] + g[b] > t - g[j] + 1e-12: continue
            h1, h2 = G - j - a, G - j - b
            if h1 < 0 or h2 < 0: continue
            if M[h1, h2] < req[0]: req = (M[h1, h2], (a, b))
    print('d12=%d/%d  requester best (a,b)=%s/%d  adversary value %.5f' % (j, G, req[1], G, req[0]))
    if req[0] > best[0]: best = (req[0], j)
print('t=%.4f two-request game value %.5f (at d12=%d/%d); > t: %s' % (t, best[0], best[1], G, best[0] > t))
