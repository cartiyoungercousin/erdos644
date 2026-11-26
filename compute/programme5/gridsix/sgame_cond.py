"""Conditional S-game rerun: the depth-3 S-game of ADAPT §2 (sgame.py, unchanged) plus an extra closure move that
marks as closing every critical triple (q, y, z) with q in (t/2, min(3-3t, 9/7-t)], y in (t-1/2, (2-t-q)/2],
z <= zmax (all orientations), i.e. what the drop-one / K-level closure would give if it held on the whole window.
[computed, grid; CONDITIONAL on that closure]   usage: py sgame_cond.py G nu zmax tlo thi steps"""
import sys, os, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'adapt'))
import sgame
G = int(sys.argv[1]); nu = float(sys.argv[2]); zmax = float(sys.argv[3])
T3 = sgame.load_static(G); gm = sgame.Game(G, T3)
orig = gm.closes
def closes(S, t):
    CL, lem, Hv = orig(S, t)
    X, Y, Z = gm.X, gm.Y, gm.Z; e = sgame.EPS
    crit = (X > t / 2 + e) & (X <= min(3 - 3 * t, 9 / 7 - t) + e) & (Y > t - 0.5 + e) & (Y <= (2 - t - X) / 2 + e) & (Z <= zmax + e)
    return CL | gm.sym(crit), lem, Hv
gm.closes = closes
for t in np.linspace(float(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6])):
    adv, S, _ = sgame.solve(G, T3, nu, t, game=gm)
    print('t=%.5f  %s  |S*|=%d  S*=%s' % (t, 'ADVERSARY' if adv else 'requester', S.sum(), sgame.compact(S, G)), flush=True)
