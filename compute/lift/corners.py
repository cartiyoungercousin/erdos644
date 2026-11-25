"""Top corners of the J = 3 steering box.  After S2 (inside B1, mass t) the adversary picks
p12 in [0, 1-t]; her S3 contains P12 and caps p13 <= c, p23 <= 2 - t - p12 - c.  At the top corner
p = 2 - t, i.e. N = 1 + t, so omega = N - 1 - t = 0: every later reply is forced (K_i = S_i) and the
anchored game is STATIC; static4 is then its exact first-order value [MILP, float].
Prints, for each p12, min over c of static4(corner)."""
import sys
import numpy as np
from anchored_lp import static4
t = eval(sys.argv[1])
n = int(sys.argv[2]) if len(sys.argv) > 2 else 7
worst = -1
for p12 in np.linspace(0, 1 - t, 4):
    tot = 2 - t - p12
    best = (9, None)
    for c in np.linspace(max(0, tot - (1 - p12)), tot / 2, n):
        sh = (p12, c, min(tot - c, 1 - c))      # B3 has mass 1: p13 + p23 <= 1 (then N > 1 + t, not static)
        v = static4(sh)
        if v < best[0]: best = (v, sh)
    worst = max(worst, best[0])
    print('t=%.4f p12=%.4f: best corner static value %.4f at %s' % (t, p12, best[0], tuple(round(z, 4) for z in best[1])), flush=True)
print('t=%.4f: J=3 top-corner value %.4f  (%s)' % (t, worst, 'ok' if worst <= t + 1e-9 else 'FAILS'))
