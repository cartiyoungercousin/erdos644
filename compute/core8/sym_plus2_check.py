"""CORE 45.1, Theorem S+ with rotating overlaps (bound u <= 4 eps k - 12): exact check of the construction.
Odd cell number r (r = 0, 1, 2 cyclically): petals r and r+1 share one point y, assigned to class-line r."""
import itertools


def check(k, T, parts, pi):
    n = sum(parts); c = n - k; assert sum(pi) == c and all(3 * p >= v for p, v in zip(pi, parts))
    kappa, P, Q = [], [[], [], []], [[], [], []]; u = 0
    for j, (v, p) in enumerate(zip(parts, pi)):
        pts = [(j, i) for i in range(v)]; kj = (3 * p - v) // 2; odd = (3 * p - v) % 2; pj = p - kj
        kappa += pts[:kj]; rest = pts[kj:]
        if odd:
            r0 = u % 3; r1 = (r0 + 1) % 3; r2 = (r0 + 2) % 3; u += 1
            y = rest[0]; r = rest[1:]; m = pj - 1
            P[r0] += [y] + r[:m]; P[r1] += [y] + r[m:2 * m]; P[r2] += r[2 * m:]; assert len(r[2 * m:]) == pj
            Q[r0] += [y] + r[:m]; Q[r1] += r[m:2 * m]; Q[r2] += r[2 * m:]
        else:
            for i in range(3): P[i] += rest[i * pj:(i + 1) * pj]; Q[i] += rest[i * pj:(i + 1) * pj]
    Ks = [frozenset(kappa + P[i]) for i in range(3)]
    prof = lambda K: tuple(sum(1 for x in K if x[0] == j) for j in range(len(parts)))
    assert all(prof(K) == tuple(pi) for K in Ks)
    best = None
    for cut in itertools.product(*[range(len(q) + 1) for q in Q]):
        a = [Q[i][:cut[i]] for i in range(3)]; b = [Q[i][cut[i]:] for i in range(3)]
        lines = [a[0] + a[1] + a[2], a[0] + b[1] + b[2], b[0] + a[1] + b[2], b[0] + b[1] + a[2]]
        mx = max(map(len, lines))
        if best is None or mx < best[0]: best = (mx, lines)
    V = [(j, i) for j, v in enumerate(parts) for i in range(v)]
    seven = Ks + [frozenset(L) for L in best[1]]
    ok = all(any(x in K and y in K for K in seven) for x, y in itertools.combinations_with_replacement(V, 2))
    print(f"k={k} T={T} n={n} cells={parts} pi={pi}: odd cells u={u}, |Q|={[len(q) for q in Q]}, largest transversal {best[0]} "
          f"(3k/4 + u/4 = {0.75 * k + u / 4}; <= T: {best[0] <= T}), pair-cover {ok}")


check(16, 13, (9, 9, 9, 4), (4, 4, 4, 3))
check(16, 14, (7, 7, 7, 5, 5, 3), (4, 4, 4, 2, 2, 2))
check(20, 17, (5, 5, 5, 5, 5, 5, 5, 3), (2, 2, 2, 2, 2, 2, 3, 3))
check(16, 14, (9, 9, 9, 4), (4, 4, 4, 3))
