r"""Independent re-run of the CORE 96 density comparison (notes/verify/thm96_1.md).  [computed float]
rho_G(N,eps) = N h(c/N) - (N-y) h((c-y)/(N-y)),  y = (delta+3eps)/2  (rate of {K : x0 notin K, Y subset K}; x0 factor polynomial)
gamma = (N-t) h(omega/(N-t))  (T-covering density floor 1/C(n-T, c-T)).
Also the elementary upper bound rho_G <= y ln(N/(c-y)) (each factor (c-i)/(n-i) >= (c-Y)/n), and the finite-k exact ratio at k = 400.
Usage: py -3.14 rates.py"""
import math
h = lambda p: 0.0 if p <= 0 or p >= 1 else -p * math.log(p) - (1 - p) * math.log(1 - p)
def rates(N, eps):
    t = .75 + eps; c = N - 1; om = N - 1 - t; d = N - 1.75; y = (d + 3 * eps) / 2
    rho = N * h(c / N) - (N - y) * h((c - y) / (N - y)); gam = (N - t) * h(om / (N - t))
    return rho, gam, y * math.log(N / (c - y)), y
print(" eps      N_lo    N_hi   max rho/gam (at N)   min gam-rho (at N)   max ub/gam   ratio at low/mid/top")
for eps in (1e-5, 1e-4, 1e-3, 0.003, 0.01, 0.02, 0.03, 0.04, 0.05, 0.06, 0.07, 0.08):
    t = .75 + eps; lo, hi = 5 * t - 2, 3 - t
    if lo >= hi: print(f"{eps}: window empty"); continue
    M = 4000; best = (0, 0); marg = (9, 0); ubm = 0; vals = []
    for i in range(1, M):
        N = lo + (hi - lo) * i / M; r, g, ub, y = rates(N, eps)
        if r / g > best[0]: best = (r / g, N)
        if g - r < marg[0]: marg = (g - r, N)
        ubm = max(ubm, ub / g)
        if i in (1, M // 2, M - 1): vals.append(r / g)
    print(f"{eps:<8} {lo:.4f} {hi:.4f}   {best[0]:.4f} ({best[1]:.4f})      {marg[0]:+.5f} ({marg[1]:.4f})       {ubm:.4f}     " + " ".join(f"{v:.3f}" for v in vals))
print("at N=2, eps->0:", [round(x, 4) for x in rates(2.0, 1e-6)[:2]])
# finite k exact: log of |C(n,c)|/C(n-1-Y, c-Y) and log C(n-T, c-T), k = 400
k = 400
for eps_k, nk in ((4, 760), (4, 800), (4, 860), (4, 896), (20, 820), (20, 850), (20, 880)):
    T = 300 + eps_k; n = nk; c = n - k; Nn = n / k; e = eps_k / k; dlt = Nn - 1.75
    Y = math.floor((dlt + 3 * e) / 2 * k) + 1
    lg = lambda a, b: math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)
    rhoG = (lg(n, c) - lg(n - 1 - Y, c - Y)) / k; gam = lg(n - T, c - T) / k
    print(f"k={k} T={T} n={n}: |Y|={Y}, rho_G={rhoG:.4f} (incl. x0 factor), gamma={gam:.4f}, ratio={rhoG/gam:.3f}, in window: {5*T-2*k < n < 3*k-T}")
