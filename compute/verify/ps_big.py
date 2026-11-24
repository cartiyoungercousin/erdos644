import random, sys
from ps_check import *
rng = random.Random(77)
tot = dict(g=0, over=0, cov=0, bad=0)
for (k, T) in [(150, 117), (200, 160), (240, 180), (120, 94)]:
    t = T / k; dmax = int(3 * t / 16 * k)
    for (dX, dY) in [(dmax, dmax), (dmax, 2), (dmax // 3, dmax), (dmax, dmax // 2 + 1)]:
        for X in (0, 1):
            hs = feasible_hits(k, T, dX, dY)
            if not hs: print('none', k, T, dX, dY); continue
            for hX in (hs[0], hs[-1]):
                for var, m in (('free', 5 * k), ('pool', 3 * k)):
                    fam = mkfam(k, T, X, hX, dX, dY, m, var)
                    st = run_family(fam, T, X, 60, rng, 'random')
                    tot['g'] += st['games']; tot['over'] += st['over']; tot['cov'] += st['covers']
                    tot['bad'] += st['wrong'] + st['trace_viol'] + st['noreply']
                    print((k, T, dX, dY, X, hX, var, m), st['games'], st['over'], st['covers'], st['wrong'], st['trace_viol'], st['noreply'], st['maxreq'], flush=True)
print('TOTAL', tot)
