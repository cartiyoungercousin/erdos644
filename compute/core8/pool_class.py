"""CORE Part VIII, section 35: the O-avoiding class with dumps inside a small pool O' of O (|O'| = sigma * omega).

Members available: K1, K2 and S + Y for q requests S avoiding O (strict: a* of A, a* of B, rest of g; free: any) and
ANY omega-subsets Y of O' of her choice (the most favourable reading of 'unpredictable inside O'').
need = min over readings (joint LP per reading), with future lines allowed useful dump <= ucap each.
Usage: py pool_class.py t N o q sigma [free] [ucap]
"""
import itertools, sys
from lpx import LP, INF
from kernel_precheck import PL, patterns


def solve(t, N, o, q, R, phi, sigma, free, ucap):
    c = N - 1; om = c - t; a = N / 2 - 0.625
    reg = {1: c - o, 2: c - o, 0: N - 2 * c + o}
    L = LP()
    y = {(X, J): L.var() for X in (0, 1, 2, 3) for J in range(1 << q)}
    for X, mX in reg.items(): L.row([(y[X, J], 1.0) for J in range(1 << q)], mX, mX)
    L.row([(y[3, J], 1.0) for J in range(1 << q)], o, o)
    L.row([(y[3, J], 1.0) for J in range(1, 1 << q)], -INF, sigma * om)                     # dumps inside O'
    for i in range(q):
        L.row([(y[3, J], 1.0) for J in range(1 << q) if J >> i & 1], om, om)
        if free: L.row([(y[X, J], 1.0) for X in (0, 1, 2) for J in range(1 << q) if J >> i & 1], t, t)
        else:
            for X, s in ((1, a), (2, a), (0, t - 2 * a)): L.row([(y[X, J], 1.0) for J in range(1 << q) if J >> i & 1], s, s)
    r = len(R); F = [f for f in range(7) if f not in phi]
    mu = {hh: [] for hh in range(1 << r)}
    for (X, J), v in y.items():
        T = X | (J << 2); hh = 0
        for i, x in enumerate(R):
            if T >> x & 1: hh |= 1 << i
        mu[hh].append(v)
    u = [L.var(0.0, ucap, 1.0) for e in range(len(F))]
    line = {e: [] for e in range(len(F))}
    for hh in range(1 << r):
        base = frozenset(phi[i] for i in range(r) if hh >> i & 1)
        cols = []
        for k in range(len(F) + 1):
            for E in itertools.combinations(range(len(F)), k):
                H = base | frozenset(F[e] for e in E)
                if any(P <= H for P in PL):
                    v = L.var(); cols.append(v)
                    for e in E: line[e].append(v)
        L.row([(v, 1.0) for v in cols] + [(v, -1.0) for v in mu[hh]], 0.0, 0.0)
    for e in range(len(F)): L.row([(v, 1.0) for v in line[e]] + [(u[e], -1.0)], -INF, t)
    val, x = L.solve()
    return val


def run(t, N, o, q, sigma, free=False, ucap=None):
    om = N - 1 - t; base = om - 4 * (t - 0.75); ucap = om if ucap is None else ucap
    best = (9.0, None, None)
    for use12 in ((), (0,), (0, 1)):
        for j in range(0, q + 1):
            R = use12 + tuple(range(2, 2 + j))
            if len(R) < 2 or len(R) > 7: continue
            for phi in patterns(len(R)):
                v = solve(t, N, o, q, R, phi, sigma, free, ucap)
                if v is not None and v < best[0] - 1e-9: best = (v, R, phi)
    return best, base


if __name__ == "__main__":
    t, N, o, q = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    for sigma in (1.0, 1.2, 1.4, 1.5, 1.7, 2.0):
        for free in (False, True):
            b, base = run(t, N, o, q, sigma, free)
            print(f"t={t} N={N} o={o} q={q} sigma={sigma} free={free}: need={b[0]:.5f} (base {base:.4f}) R={b[1]} labels={b[2]}", flush=True)
