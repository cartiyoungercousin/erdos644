"""PETAL §41.3: the triangle family (three arena classes, pairwise regions sharing atoms a, common core b, leak rho).
Exact LP check that SL0 (h <= tau and beta <= d) fails while SL1 holds with A = union."""
from fractions import Fraction as Fr
import numpy as np
from multiarena import evaluate
from ma_sl0_opt import sl0gap
AT = [(0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]
for (rho, a, b) in [(Fr(1, 20), Fr(1, 20), Fr(123, 100)), (Fr(1, 20), Fr(1, 40), Fr(1255, 1000)), (Fr(1, 10), Fr(1, 40), Fr(1205, 1000))]:
    c = 2 - 2 * rho - 3 * a - b; tau = 2 * a + b - 1 + rho; d = 1 - c - tau   # case 2a <= 1 - rho
    U = 3 * a + b; costU = (U - 1 + rho) + Fr(8, 3) * rho; arena = tau + Fr(8, 3) * d
    s = np.array([0, 0, 0, float(a), float(a), float(a), float(b)]); r = np.array([float(rho)] * 3)
    g, e = sl0gap(s, r, AT, 3)
    print('rho a b', rho, a, b, '| c', c, float(c), 'tau', tau, float(tau), 'd', d, '| LP c %.4f tau %.4f' % (e['c'], e['tau']),
          '| SL0 gap (min beta at h<=tau) - d = %.4f (hand: a/2 = %.4f... see note)' % (g, float(a) / 2),
          '| cost(U) =', float(costU), 'arena bound', float(arena), 'phi LP (t=3/4) %.4f' % e['phi'])
