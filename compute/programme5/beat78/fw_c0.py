"""Frankl-Wilson pair existence (PAPER Thm 9.6) needs r <= c0(nu) k and p ~ (k+r)/2 <= k.  Compare with the
covering radius forced at eps <= 1/8: rho = nu - 7/4 - eps >= nu - 15/8.  c0 = root of
nu h(1/nu) - (1+rho) h(rho/(1+rho)) - nu h((1+rho)/(2nu)) (h = binary entropy, nats).  usage: py -3.14 fw_c0.py"""
import math, os
def h(x): return 0.0 if x <= 0 or x >= 1 else -x * math.log(x) - (1 - x) * math.log(1 - x)
def F(nu, r): return nu * h(1 / nu) - (1 + r) * h(r / (1 + r)) - nu * h(min(1, (1 + r) / (2 * nu)))
def c0(nu):
    lo, hi = 0.0, 1.0
    if F(nu, hi) > 0: return 1.0
    for _ in range(80):
        m = (lo + hi) / 2
        if F(nu, m) > 0: lo = m
        else: hi = m
    return lo
out = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'logs', 'fw_c0.log'), 'w')
for nu in [2.0, 2.2, 2.3, 2.4, 2.5, 2.6, 2.7, 2.8, 2.9, 3.0, 4.0, 10.0]:
    s = 'nu=%.2f  c0=%.4f  rho_min(eps<=1/8)=%.4f  FW usable: %s' % (nu, c0(nu), nu - 15 / 8, c0(nu) >= nu - 15 / 8)
    print(s); print(s, file=out)
