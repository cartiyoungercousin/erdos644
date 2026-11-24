"""Part X (CORE §50-§54): exponents for spread approximation (Kupavskii-Zakharov Lemma 10) in the core window.
Units k = 1; first-order exponents (nats per k) from exact log-binomials at k = K (lgamma), plus the entropy form.
py compute/spread/spread_params.py
"""
from math import log, exp, lgamma

def h(p):
    return 0.0 if p <= 0 or p >= 1 else -p*log(p) - (1-p)*log(1-p)

def lC(a, b):
    return lgamma(a+1) - lgamma(b+1) - lgamma(a-b+1)

def row(t, N, K=4000):
    c = N - 1; om = N - 1 - t
    e = lambda a, b: lC(a*K, b*K) / K           # first-order log-binomial
    r_max = N / c                               # max spreadness of any c-uniform family on V
    gam = e(N - t, om)                          # ln(|A| * max nu(K)) = ln C(n-T, omega): minimal family has density e^{-gam k}
    gam_h = (N - t) * h(om / (N - t))
    tau_triv = exp(e(N, c) / c)                 # every measure is tau-homogeneous for tau >= this (x = c is the binding X)
    tau0 = exp(gam / c)                         # X = K test: a member carrying the maximal request mass is homogeneous iff tau >= tau0
    tau_pool = exp(-(e(N - om, c - om) - e(N, c)) / om)   # the pool family's head Y (|Y| = omega) is selected iff tau < tau_pool
    taum = (tau0 * tau_pool) ** 0.5             # representative tau in the useful range (tau0, tau_pool), when nonempty
    qlo = gam / log(tau_triv); qm = gam / log(taum)   # head size needed for Lemma 10's remainder bound < 1
    Phi = e(N - om, t - 0.5) + 1.5 * log(3)     # ln #(pencil frames whose kernel contains a fixed head of mass omega)
    rho_req = e(N, t)                           # ln #requests
    rho_hom = -om * log(taum) - (e(N - om, c - om) - e(N, c))   # head of a class of nu-mass e^{-rho k} is selected iff rho <= rho_hom
    return dict(tau_pool=tau_pool, N=N, om=om, r_max=r_max, gam=gam, gam_h=gam_h, tau0=tau0, tau_triv=tau_triv, taum=taum,
                qlo=qlo, qm=qm, Tk2=t - 0.5, Phi=Phi, rho_req=rho_req, rho_hom=rho_hom)

if __name__ == "__main__":
    t = 0.76
    print("t=%.2f  window N in (%.3f, %.3f)" % (t, 3*t - 0.5, 3 - t))
    print("N     omega  n/c    gamma  (entropy) tau0   tau_pool tau_m  tau_triv  q_lo   q(tau_m)  c     T-k/2  Phi/2  rho_req rho_hom")
    for N in [1.79, 1.82, 1.85, 1.9, 2.0, 2.1, 2.2, 2.23]:
        r = row(t, N)
        print("%.2f  %.3f  %.3f  %.3f  (%.3f)   %.3f  %.3f    %.3f  %.3f     %.3f  %.3f     %.2f  %.2f   %.3f  %.3f   %.3f" % (
            N, r['om'], r['r_max'], r['gam'], r['gam_h'], r['tau0'], r['tau_pool'], r['taum'], r['tau_triv'], r['qlo'], r['qm'],
            N - 1, r['Tk2'], r['Phi']/2, r['rho_req'], r['rho_hom']))
        assert 1 < r['tau0'] < r['tau_triv'] and r['r_max'] < 32
        if r['tau0'] >= r['tau_pool']:
            print("      DEGENERATE: tau0 >= tau_pool: no tau both detects the pool head and lets a minimal-family member be headless"); continue
        assert 0 < r['rho_hom'] < r['Phi']/2 < r['rho_req']
    print("asserts: 1 < tau0 < tau_triv; n/c < 32 (Tao/ALWZ bound vacuous); 0 < rho_hom < Phi/2 < rho_req where non-degenerate: OK")
    for t in [0.751, 0.755, 0.76, 0.77, 0.8]:
        f = lambda N: log(row(t, N)['tau0']) - log(row(t, N)['tau_pool'])
        lo, hi = 3*t - 0.5 + 1e-3, 3 - t - 1e-3
        if f(lo) > 0 or f(hi) < 0: print("t=%.3f no sign change: f(lo)=%.3f f(hi)=%.3f" % (t, f(lo), f(hi))); continue
        for _ in range(60):
            m = (lo + hi)/2
            lo, hi = (m, hi) if f(m) < 0 else (lo, m)
        print("t=%.3f  window (%.4f, %.4f)  useful tau-range empty for N >= N* = %.4f" % (t, 3*t - 0.5, 3 - t, lo))
