"""CORE 39.4, Theorem S+ (odd cells): exact check of the construction.  K has profile pi >= v/3; kappa_j = floor((3pi_j - v_j)/2);
in odd cells petals 1, 2 share one point y_j, assigned to line 1.  Checks: K1, K2, K3 have profile pi, the four transversal
lines have size <= T, and K1, K2, K3 + the four lines (unpadded = worst case, by monotonicity 1.1) cover all pairs."""
import itertools


def check(k, T, parts, pi):
    n = sum(parts); c = n - k; assert sum(pi) == c and all(3 * p >= v for p, v in zip(pi, parts))
    kappa, P, Q = [], [[], [], []], [[], [], []]
    for j, (v, p) in enumerate(zip(parts, pi)):
        pts = [(j, i) for i in range(v)]; kj = (3 * p - v) // 2; odd = (3 * p - v) % 2; pj = p - kj
        kappa += pts[:kj]; rest = pts[kj:]
        if odd:
            y = rest[0]; r = rest[1:]; m = pj - 1
            P[0] += [y] + r[:m]; P[1] += [y] + r[m:2 * m]; P[2] += r[2 * m:]; assert len(r[2 * m:]) == pj
            Q[0] += [y] + r[:m]; Q[1] += r[m:2 * m]; Q[2] += r[2 * m:]
        else:
            for i in range(3): P[i] += rest[i * pj:(i + 1) * pj]; Q[i] += rest[i * pj:(i + 1) * pj]
    Ks = [frozenset(kappa + P[i]) for i in range(3)]
    prof = lambda K: tuple(sum(1 for x in K if x[0] == j) for j in range(len(parts)))
    assert all(prof(K) == tuple(pi) for K in Ks)
    best = None
    for cut in itertools.product(*[range(len(q) + 1) for q in Q]):          # sizes of a_i; minimise the largest transversal
        a = [Q[i][:cut[i]] for i in range(3)]; b = [Q[i][cut[i]:] for i in range(3)]
        lines = [a[0] + a[1] + a[2], a[0] + b[1] + b[2], b[0] + a[1] + b[2], b[0] + b[1] + a[2]]
        mx = max(map(len, lines))
        if best is None or mx < best[0]: best = (mx, lines)
    V = [(j, i) for j, v in enumerate(parts) for i in range(v)]
    seven = Ks + [frozenset(L) for L in best[1]]
    ok = all(any(x in K and y in K for K in seven) for x, y in itertools.combinations_with_replacement(V, 2))
    print(f"k={k} T={T} n={n} parts={parts} pi={pi}: |kappa|={len(kappa)}, largest transversal {best[0]} (<= T: {best[0] <= T}), pair-cover {ok}")


check(8, 7, (9, 7), (4, 4))
check(8, 7, (9, 6, 1), (4, 3, 1))
check(12, 10, (11, 7, 4, 1), (4, 4, 2, 1))
check(16, 13, (10, 9, 7, 3, 1), (4, 4, 3, 2, 1))
