"""CORE Part VIII, section 34.2: the triangle-type class is inert.

Pair K1, K2.  q requests, each strictly triangle-type (nothing of O, x of A, x of B, t - 2x of g; x = a* - shift),
each answered by a dump INSIDE O; she chooses the requests' mutual position AND all overlaps of the dumps
(variables z_J on O with every request receiving exactly omega).  need = min over readings among the 2 + q members
(joint LP per reading, exact for the reading).  Lemma's method predicts need < base when dumps are disjoint.
Usage: py tri_class.py t N o q [shift]
"""
import itertools, sys
from lpx import LP, INF
from kernel_precheck import PL, patterns


def solve(t, N, o, q, R, phi, shift=0.0, free_private=False):
    c = N - 1; om = c - t; a = N / 2 - 0.625 - shift
    reg = {1: c - o, 2: c - o, 0: N - 2 * c + o}
    L = LP()
    y = {(X, J): L.var() for X in (0, 1, 2, 3) for J in range(1 << q)}
    for X, mX in reg.items(): L.row([(y[X, J], 1.0) for J in range(1 << q)], mX, mX)
    L.row([(y[3, J], 1.0) for J in range(1 << q)], o, o)
    for i in range(q):
        L.row([(y[3, J], 1.0) for J in range(1 << q) if J >> i & 1], om, om)             # dump of request i, inside O
        if free_private:
            L.row([(y[X, J], 1.0) for X in (0, 1, 2) for J in range(1 << q) if J >> i & 1], t, t)
        else:
            for X, s in ((1, a), (2, a), (0, t - 2 * a)):
                L.row([(y[X, J], 1.0) for J in range(1 << q) if J >> i & 1], s, s)
    r = len(R); F = [f for f in range(7) if f not in phi]
    mu = {hh: [] for hh in range(1 << r)}
    for (X, J), v in y.items():
        T = X | (J << 2); hh = 0
        for i, x in enumerate(R):
            if T >> x & 1: hh |= 1 << i
        mu[hh].append(v)
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
        L.row([(v, 1.0) for v in cols] + [(v, -1.0) for v in mu[hh]], 0.0, 0.0)
    for e in range(len(F)): L.row([(v, 1.0) for v in line[e]] + [(u[e], -1.0)], -INF, t)
    val, x = L.solve()
    if val is None: return None, None
    return val, {k: x[v] for k, v in y.items()}


def run(t, N, o, q, shift=0.0, free_private=False):
    om = N - 1 - t; base = om - 4 * (t - 0.75)
    best = (9.0, None, None, None); cnt = 0
    for use12 in ((), (0,), (0, 1)):
        for j in range(0, q + 1):
            R = use12 + tuple(range(2, 2 + j))
            if len(R) < 2 or len(R) > 7: continue
            for phi in patterns(len(R)):
                cnt += 1
                v, yy = solve(t, N, o, q, R, phi, shift, free_private)
                if v is not None and v < best[0] - 1e-9: best = (v, R, phi, yy)
    print(f"t={t} N={N} o={o:.4f} omega={om:.3f} base={base:.4f} q={q} shift={shift:.4f} free={free_private}: min need={best[0]:.6f} "
          f"R={best[1]} labels={best[2]} ({cnt} LPs)", flush=True)
    return best


if __name__ == "__main__":
    t, N, o, q = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    shift = float(sys.argv[5]) if len(sys.argv) > 5 else 0.0
    run(t, N, o, q, shift, free_private=len(sys.argv) > 6)
