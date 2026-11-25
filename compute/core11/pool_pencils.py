r"""CORE 86.4: pencil density of the pool family vs the random threshold family.  [computed float]
Pool family P_Y = all co-edges containing Y, |Y| = omega (T-covering; Theorem S family, beaten only by pencils).
log e(G_pen[P_Y]) = max over kap of (1+t) H(kap-omega, p/3 x3, s/3 x3)  (pencil kernel must contain Y, since every member does).
rel = log e(G_pen[P_Y]) - log e(G_pen)   vs   random threshold family: -3 gamma ; and eps* from container_scales."""
import math, sys
sys.path.insert(0, '.')
from container_scales import h, ent_mass, pencil
for t in (0.7501, 0.76, 0.78):
    lo, hi = 3*t - 0.5, 3 - t
    for i in range(0, 11, 2):
        N = lo + (hi - lo)*(i + 0.5)/11; c = N - 1; om = c - t; g = (N - t)*h(om/(N - t)); LX = N*h(1/N)
        best = None
        for j in range(401):
            kap = N - 2*t + j*((N - 1.5) - (N - 2*t))/400
            if kap < om: continue
            p = 2*N - 3 - 2*kap; s = 3 - N + kap
            if p < -1e-12 or s < -1e-12: continue
            v = ent_mass([kap - om] + [p/3]*3 + [s/3]*3)
            best = v if best is None else max(best, v)
        eP, D2 = pencil(N, c, t)
        L2 = eP - LX - D2; L3 = eP - LX; epsP = min(L2 - g, L3 - 2*g)
        print(f"t={t} N={N:.4f}: pool rel = {best - eP:+.4f}  random rel = {-3*g:+.4f}  -eps* = {-epsP:+.4f}  "
              f"pool family size exp = {(1+t)*h(t/(1+t)):.4f} vs min {LX-g:.4f}")
