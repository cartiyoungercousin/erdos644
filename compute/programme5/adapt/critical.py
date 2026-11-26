"""General depth-1 search (depth1.py) on the critical pair q ~ 3/7 below 6/7: for each surviving answer (y,z) to her best
DUMP from q, try all structured requests (step 1/24) against the heuristic spoiler.  usage: py -3.14 critical.py G t qi"""
import sys, random, numpy as np
import sgame, depth1, survivors
G, t, qi = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
T3 = sgame.load_static(G); gm = sgame.Game(G, T3)
adv, S, (CL, lem, Hv) = sgame.solve(G, T3, 1000, t, game=gm)
print('S* =', sgame.compact(S, G), flush=True)
box, ans = survivors.surviving_answers(gm, S, t, 1000, CL, qi)
print('q=%d/%d box %s: %d surviving answers' % (qi, G, box, len(ans)), flush=True)
inS = lambda v: S[min(G, int(round(v * G)))] and abs(v * G - round(v * G)) < 1e-6
rng = random.Random(0)
closed = 0
for (a, b) in sorted(ans, key=lambda p: -(p[0] + p[1]))[:8]:
    cells = (gm.g[qi], gm.g[a], gm.g[b]); found = None
    for U in survivors.requests(cells, t, 1 / 24):
        r = depth1.spoil(cells, U, t, inS, rng, G=G, tries=30)
        if r is not None and len(r) == 3 and r[1] <= t + 1e-9: found = (U, r[1]); break
    closed += found is not None
    print('  answer (%d,%d)/%d: %s' % (a, b, G, ('candidate closure U=%s' % {k: round(v, 4) for k, v in found[0].items()}) if found else 'no closure found'), flush=True)
print('closed %d of the 8 largest answers' % closed)
