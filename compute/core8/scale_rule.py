"""CORE Part VIII, section 35: static test of the 'scale rule' (a coreless high rule on the O-avoiding class).

Pair K1, K2 (O of mass o, A, B, g).  Rule on requests S with S & O = 0:  D(S) = psi(S), psi a measure-scaling bijection
V minus O -> O' (O' inside O, |O'| = omega (N - o)/t), so |D(S)| = omega for every such S and D(S) & D(S') = psi(S & S'):
no two dumps are disjoint or nested unless the requests are, and there is no common core at all.
Question: is there a Fano certificate made of a kept set R inside {K1, K2, K(S_1), ..., K(S_q)} and 7 - |R| further lines
that are pure requests (mass <= t + u_f; u_f = 0 means no help from any dump)?  need = min sum u_f, jointly over her
choice of S_1..S_q (exact for each labelling: one LP).  need = 0 is a static win against the rule.
Usage: py scale_rule.py t N o q
"""
import itertools, sys
from lpx import LP, INF
from kernel_precheck import PL, patterns


def solve(t, N, o, q, R, phi, ucap=None):
    """R: kept members, as indices 0 (K1), 1 (K2), 2.. (in-class requests 0..q-1)"""
    c = N - 1; om = c - t; rho = om / t
    oprime = om * (N - o) / t
    assert oprime <= o + 1e-12
    reg = {1: c - o, 2: c - o, 0: N - 2 * c + o}
    L = LP()
    y = {(X, J): L.var() for X in reg for J in range(1 << q)}
    for X, mX in reg.items(): L.row([(y[X, J], 1.0) for J in range(1 << q)], mX, mX)
    for i in range(q): L.row([(y[X, J], 1.0) for X in reg for J in range(1 << q) if J >> i & 1], t, t)
    m = {}                                             # full type (bits 0,1 = K1,K2; bits 2.. = requests) -> (terms, const)
    def add(T, terms, const):
        a = m.get(T, ([], 0.0)); m[T] = (a[0] + terms, a[1] + const)
    for X in reg:
        for J in range(1 << q):
            add(X | (J << 2), [(y[X, J], 1.0)], 0.0)
            add(3 | (J << 2), [(y[X, J], rho)], 0.0)       # its image in O'
    add(3, [], o - oprime)
    r = len(R); F = [f for f in range(7) if f not in phi]
    mu = {hh: ([], 0.0) for hh in range(1 << r)}
    for T, (terms, const) in m.items():
        hh = 0
        for i, x in enumerate(R):
            if T >> x & 1: hh |= 1 << i
        mu[hh] = (mu[hh][0] + terms, mu[hh][1] + const)
    u = [L.var(0.0, om if ucap is None else ucap, 1.0) for e in range(len(F))]
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


def run(t, N, o, q, verbose=True):
    om = N - 1 - t; base = om - 4 * (t - 0.75)
    best = (9.0, None, None, None); cnt = 0
    for use12 in ((), (0,), (0, 1)):                    # K2 alone is the mirror image of K1 alone
        R = use12 + tuple(range(2, 2 + q))
        for phi in patterns(len(R)):
            cnt += 1
            v, yy = solve(t, N, o, q, R, phi)
            if v is not None and v < best[0] - 1e-9: best = (v, R, phi, yy)
    if verbose:
        print(f"t={t} N={N} o={o:.4f} omega={om:.3f} base={base:.4f} q={q}: min need={best[0]:.6f} R={best[1]} labels={best[2]} ({cnt} LPs)", flush=True)
    return best


if __name__ == "__main__":
    t, N, o, q = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    b = run(t, N, o, q)
    if len(sys.argv) > 5 and b[3]:
        for (X, J), v in sorted(b[3].items()):
            if v > 1e-7: print("  region", {1: "A", 2: "B", 0: "g"}[X], "in requests", [i + 1 for i in range(q) if J >> i & 1], round(v, 5))
