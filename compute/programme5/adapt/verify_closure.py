"""Exhaustive check (grid 1/H over his free cell masses) of a claimed general depth-1 closure (depth1.py) of a triple.
usage: py -3.14 verify_closure.py t x y z uX uY uZ uE uF uG H"""
import sys, itertools, numpy as np
import depth1
t, x, y, z, uX, uY, uZ, uE, uF, uG = map(float, sys.argv[1:11]); H = int(sys.argv[11])
U = dict(X=uX, Y=uY, Z=uZ, E=uE, F=uF, G=uG)
tot = dict(X=x, Y=y, Z=z, E=1 - x - y, F=1 - x - z, G=1 - y - z)
cap = {c: max(0.0, tot[c] - U[c]) for c in tot}
rng = {c: [i / H for i in range(int(cap[c] * H + 1e-9) + 1)] + ([cap[c]] if cap[c] * H % 1 > 1e-9 else []) for c in tot}
worst, n = (None, -1), 0
for vals in itertools.product(*[rng[c] for c in 'XYZEFG']):
    K = dict(zip('XYZEFG', vals))
    if sum(vals) > 1 + 1e-12: continue
    if any(tr >= 1 - 1e-12 for tr in depth1.traces(K)): continue
    v = depth1.value((x, y, z), U, K); n += 1
    if v > worst[1]: worst = (K, v)
print('answers checked %d, worst value %.5f at %s, t=%.5f -> %s' % (n, worst[1], worst[0], t,
      'CLOSES on the grid' if worst[1] <= t + 1e-9 else 'SPOILED'))
