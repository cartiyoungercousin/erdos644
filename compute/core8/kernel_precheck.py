"""CORE Part VIII, section 34: pre-check of the kernel lemma (first-order model, units k = 1, float LP via pulp/HiGHS).

Position: free pair K1, K2 (O = K1&K2 of mass o, A, B private, g outside).  Two requests S, S' with S&O = S'&O = 0
(any masses in A, B, g, any mutual position - her variables), replies K3 = S + D, K4 = S' + D' with D, D' inside O,
|D & D'| = theta.  For every reading R (kept subset of the four replies, |R| >= 2, with a Fano labelling) the LP
    need_R = min sum_f u_f : every final co-type contains a pencil, future line f has mass <= t + u_f, 0 <= u_f <= omega
is solved JOINTLY with her request variables, so the minimum over all such (S, S') is exact for each reading.
Output: min over readings, for theta = 0 (disjoint) ... omega (nested).  The kernel lemma's method predicts
value < base for theta = 0.
Usage: py kernel_precheck.py t N o
"""
import itertools, sys
from lpx import LP, INF

PL = [frozenset(p) for p in [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]]


def patterns(r):
    seen = {}
    for phi in itertools.permutations(range(7), r):
        key = frozenset(frozenset(i for i in range(r) if phi[i] in P) for P in PL if sum(phi[i] in P for i in range(r)) == 3)
        if key not in seen: seen[key] = phi
    return list(seen.values())


def solve(t, N, o, theta, R, phi, symmetric=False):
    c = N - 1; om = c - t
    reg = {1: c - o, 2: c - o, 0: N - 2 * c + o}          # A (bit1), B (bit2), g
    L = LP()
    y = {(X, a, b): L.var() for X in reg for a in (0, 1) for b in (0, 1)}
    for X, mX in reg.items(): L.row([(y[X, a, b], 1.0) for a in (0, 1) for b in (0, 1)], mX, mX)
    L.row([(y[X, 1, b], 1.0) for X in reg for b in (0, 1)], t, t)
    L.row([(y[X, a, 1], 1.0) for X in reg for a in (0, 1)], t, t)
    if symmetric:
        a_star = N / 2 - 0.625
        for X in (1, 2):
            L.row([(y[X, 1, 0], 1.0), (y[X, 1, 1], 1.0)], a_star, a_star); L.row([(y[X, 0, 1], 1.0), (y[X, 1, 1], 1.0)], a_star, a_star)
    # type masses (4-bit co-types: bit0 K1, bit1 K2, bit2 K3, bit3 K4): lists of (var, coef) plus constant
    m = {}
    for X in reg:
        for a in (0, 1):
            for b in (0, 1): m[X | (a << 2) | (b << 3)] = ([(y[X, a, b], 1.0)], 0.0)
    m[3] = ([], o - 2 * om + theta); m[3 | 4] = ([], om - theta); m[3 | 8] = ([], om - theta); m[15] = ([], theta)
    r = len(R); F = [f for f in range(7) if f not in phi]
    mu = {hh: ([], 0.0) for hh in range(1 << r)}
    for J, (terms, const) in m.items():
        hh = 0
        for i, x in enumerate(R):
            if J >> x & 1: hh |= 1 << i
        mu[hh] = (mu[hh][0] + terms, mu[hh][1] + const)
    u = [L.var(0.0, om, 1.0) for e in range(len(F))]
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
        L.row([(v, 1.0) for v in cols] + [(v, -cf) for v, cf in mu[hh][0]], mu[hh][1], mu[hh][1])
    for e in range(len(F)): L.row([(v, 1.0) for v in line[e]] + [(u[e], -1.0)], -INF, t)
    val, x = L.solve()
    if val is None: return None, None
    return val, {k: x[v] for k, v in y.items()}


def run(t, N, o, thetas=None, symmetric=False, verbose=True):
    om = N - 1 - t; base = om - 4 * (t - 0.75)
    res = []
    for th in (thetas if thetas is not None else [0, om / 4, om / 2, 3 * om / 4, om]):
        best = (9.0, None, None, None)
        for r in (2, 3, 4):
            for R in itertools.combinations(range(4), r):
                for phi in patterns(r):
                    v, yy = solve(t, N, o, th, R, phi, symmetric=symmetric)
                    if v is not None and v < best[0] - 1e-9: best = (v, R, phi, yy)
        res.append((th, best[0]))
        if verbose: print(f"t={t} N={N} o={o:.4f} omega={om:.3f} base={base:.4f}  theta/omega={th/om:.2f}  value={best[0]:.6f}  "
              f"reading R={best[1]} labels={best[2]}", flush=True)
    return res


if __name__ == "__main__":
    t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    run(t, N, o, symmetric=len(sys.argv) > 4)
