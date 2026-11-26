"""Bisection in t for the S-game value at given nu (grid G).  usage: py -3.14 scan_nu.py G nu [lo hi steps]"""
import sys, numpy as np
import sgame
G = int(sys.argv[1]); nu = float(sys.argv[2])
lo, hi, steps = (float(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (0.76, 0.90, 9)
T3 = sgame.load_static(G); gm = sgame.Game(G, T3)
adv_lo, _, _ = sgame.solve(G, T3, nu, lo, game=gm)
adv_hi, Shi, _ = sgame.solve(G, T3, nu, hi, game=gm)
print('nu=%g G=%d  t=%.5f: %s   t=%.5f: %s' % (nu, G, lo, 'ADV' if adv_lo else 'REQ', hi, 'ADV' if adv_hi else 'REQ'), flush=True)
Slo = None
for _ in range(steps):
    mid = (lo + hi) / 2
    adv, S, _ = sgame.solve(G, T3, nu, mid, game=gm)
    print('  t=%.5f eps=%.5f %s |S*|=%d %s' % (mid, mid - .75, 'ADV' if adv else 'REQ', S.sum(), sgame.compact(S, G)), flush=True)
    if adv: lo, Slo = mid, S
    else: hi = mid
print('RESULT nu=%g G=%d: adversary survives up to t=%.5f, requester wins from t=%.5f  (eps* in [%.5f, %.5f]; 3/28=%.5f)' % (
    nu, G, lo, hi, lo - .75, hi - .75, 3 / 28), flush=True)
