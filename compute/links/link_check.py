r"""CORE §100-§104: links (requests S forced into every member) and traces.

exact : sympy identities (slack under links, region moves, pool sigma bound, gamma invariance).  [computed exact]
milp  : pool family {K >= Y}, |Y| = omega, inside the link at S (|S| = s): static certificates of order r = 1..7 at
        (N - s, t - s); and bare r = 2 certificates in the link.  Uses window_density.cert (scipy/HiGHS). [computed float]
usage: py -3.14 link_check.py exact | milp
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'strip'))


def exact():
    import sympy as sp
    N, t, s, u, q = sp.symbols('N t s u q')
    eps = t - sp.Rational(3, 4); dl = N - sp.Rational(7, 4); om = N - 1 - t
    S = lambda N_, t_: (q - 3) * (N_ - sp.Rational(7, 4)) + (7 - q) * (t_ - sp.Rational(3, 4))
    print("S_q(N,t) - [q c + (7-q) t - 3N]           =", sp.simplify(S(N, t) - (q * (N - 1) + (7 - q) * t - 3 * N)))
    print("S_q(N-s,t-s) - S_q(N,t)                   =", sp.simplify(S(N - s, t - s) - S(N, t)))
    print("S_2(N,t) - (4 eps - omega)                =", sp.simplify(S(N, t).subs(q, 2) - (4 * eps - om)))
    print("omega(N-s,t-s) - omega                    =", sp.simplify((N - s - 1 - (t - s)) - om))
    print("eps(t-s) - eps                            =", sp.simplify((t - s - sp.Rational(3, 4)) - eps))
    print("strip margin (5t-2-N) change under link   =", sp.simplify((5 * (t - s) - 2 - (N - s)) - (5 * t - 2 - N)))
    print("crowded margin (3t-1/2-N) change          =", sp.simplify((3 * (t - s) - sp.Rational(1, 2) - (N - s)) - (3 * t - sp.Rational(1, 2) - N)))
    print("petal margin (N+t-3) change               =", sp.simplify(((N - s) + (t - s) - 3) - (N + t - 3)))
    print("N-t (fixes gamma) change                  =", sp.simplify(((N - s) - (t - s)) - (N - t)))
    print("pool: (1-t) - (3t-N)/2 - (omega-4eps)/2   =", sp.simplify((1 - t) - (3 * t - N) / 2 - (om - 4 * eps) / 2))
    print("pool waste in link: 4 omega - 4 delta'    =", sp.factor(sp.expand(4 * om - 4 * (dl - s))), " (>0 iff s > eps)")
    print("trace on W (u = N-w): S_q(w,t) - S_q(N,t) =", sp.simplify(S(N - u, t) - S(N, t)))


def milp():
    from window_density import cert
    t = 0.76; e = t - 0.75
    print("t =", t, "eps =", e)
    for N in [1.80, 1.85, 1.90, 2.00, 2.10]:
        om = N - 1 - t
        for f in [0.0, 0.5, 0.9, 1.1, 1.5, 3.0]:
            s = f * e; Np, tp = N - s, t - s
            pool = [r for r in range(1, 8) if cert(Np, tp, r, y=om)]
            bare2 = cert(Np, tp, 2)
            print(f"N={N:.2f} s={f:.1f}eps  link (N',t')=({Np:.4f},{tp:.4f}) omega'={om:.3f} "
                  f"pool-in-link certs r={pool}  bare r=2 cert: {bare2}  (strip test N'<=5t'-2: {Np <= 5*tp-2+1e-12})",
                  flush=True)


if __name__ == '__main__':
    {'exact': exact, 'milp': milp}[sys.argv[1]]()
