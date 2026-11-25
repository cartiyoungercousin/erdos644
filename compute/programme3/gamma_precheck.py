r"""PROGRAMME3_GAMMA precheck: density exponents gamma = ln(1/p)/k and Fourier damping cutoffs in the window.
All exponents are nats per k (asymptotic, k -> oo) unless a finite k is named.
Usage: py -3.14 gamma_precheck.py
"""
import math
from math import log, comb, lgamma

L7 = log(7.0)

def h(y):                     # binary entropy, nats
    if y <= 0 or y >= 1: return 0.0
    return -y * log(y) - (1 - y) * log(1 - y)

def ent(N, x):                # (1/k) ln C(Nk, xk), asymptotic
    return N * h(min(x, N) / N)

def root(f, lo, hi, it=200):  # f(lo) > 0 > f(hi)
    for _ in range(it):
        m = (lo + hi) / 2
        if f(m) > 0: lo = m
        else: hi = m
    return (lo + hi) / 2

def lnC(a, b): return lgamma(a + 1) - lgamma(b + 1) - lgamma(a - b + 1)

def cell(N, eps, eta=0.5):
    d = N - 1.75; om = d - eps
    feas = om >= 0 and d >= 3 * eps - 1e-12 and N < 11 / 6
    if om < 0: return dict(N=N, eps=eps, d=d, om=om, feas=False, vacuous=True)
    ga = (1 + om) * h(om / (1 + om))                     # (1/k) ln C(k+r, k): minimal covering density
    out = dict(N=N, eps=eps, d=d, om=om, feas=feas, vacuous=False, ga=ga, emax=ga / log(2))
    for k in (100, 1000):                                # finite-k: exact (a), random (b) = (a) - ln ln C(n, k+r)
        n, r = round(N * k), round(om * k)
        a = lnC(k + r, k) / k
        out[f"ga{k}"] = a; out[f"gb{k}"] = max(0.0, a - log(lnC(n, k + r)) / k)
    g = ga
    x1 = 2 * g / L7                                      # brief: 7^{-w/2} < p
    x2 = root(lambda x: ent(N, x) - x * L7 / 2, 1e-9, N)          # |c_h|<=1 union: C(n,w) 7^{-w/2} < 1
    x3 = root(lambda x: ent(N, x) + g - x * L7, 1e-9, N)          # Cauchy-Schwarz + Parseval: C(n,w)/p * 7^{-w} < 1
    out.update(x1=x1, c1=ent(N, x1), x2=x2, c2=ent(N, min(x2, N / 2)), x3=x3, c3=ent(N, min(x3, N / 2)))
    xs = [i / 10000 * N for i in range(1, 10000)]                  # wall: Linf pseudorandomness needs eta < e^{-c' k}
    out["cw"] = max(ent(N, x) - x * L7 / 2 for x in xs)
    out["cw1"] = max(ent(N, x) - x * L7 / 2 for x in xs if x <= x1) if x1 > xs[0] else 0.0   # same, light range only
    gh = N * h(1 / N) - (N - om) * h(1 / (N - om))                # head/greedy families (CORE 56): P(first omega*k of an order avoid B)
    out.update(gh=gh, xh=2 * gh / L7, ch=ent(N, 2 * gh / L7))
    steps = g / log(1 + eta)                                       # increments per k
    out.update(steps=steps, slack=(4 * d / steps if steps > 1e-9 else float("inf")), oddmax=12 * d / 7)
    return out

if __name__ == "__main__":
    print("N     eps   delta  omega  feas | g_a    g_a100 g_b100 g_b1000 e_max/k | x1     c1    | x2    c2    | x3    c3    | 4eps  | c_wall cw_lt | g_head x_head c_head | steps/k slack/step oddmax/k")
    for N in (1.76, 1.78, 1.80, 1.82):
        for eps in (0.01, 0.03, 0.05):
            o = cell(N, eps)
            if o["vacuous"]:
                print(f"{N:.2f}  {eps:.2f}  {o['d']:.3f}  {o['om']:+.3f} VACUOUS (n-T<k)"); continue
            print(f"{N:.2f}  {eps:.2f}  {o['d']:.3f}  {o['om']:.3f}  {'yes' if o['feas'] else 'C1x'} | "
                  f"{o['ga']:.4f} {o['ga100']:.4f} {o['gb100']:.4f} {o['gb1000']:.4f}  {o['emax']:.3f}  | "
                  f"{o['x1']:.4f} {o['c1']:.3f} | {o['x2']:.3f} {o['c2']:.3f} | {o['x3']:.3f} {o['c3']:.3f} | "
                  f"{4*eps:.2f} | {o['cw']:.3f} {o['cw1']:.3f} | {o['gh']:.4f} {o['xh']:.4f} {o['ch']:.3f} | {o['steps']:.3f}  {o['slack']:.3f} {o['oddmax']:.4f}")
    # window extremes
    for N, eps in ((11 / 6 - 1e-9, 0.0), (1.75 + 3 * 0.005, 0.005), (1.75 + 3 * 0.001, 0.001)):
        o = cell(N, eps); print(f"extreme N={N:.4f} eps={eps}: g_a={o['ga']:.4f} x1={o['x1']:.4f} 4eps={4*eps:.3f} delta={o['d']:.4f} slack/step={o['slack']:.3f}")
