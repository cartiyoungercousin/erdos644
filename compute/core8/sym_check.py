"""CORE Part VIII, Theorem S (symmetric families lose): exact brute-force check on small profile families.
Family = all c-sets whose profile w.r.t. a partition lies in PI; T-covering checked; then the rotation pencil
(kappa = (3 pi - v)/2, three petals (v - pi)/2) plus the four transversal requests, EVERY choice of replies from the family.
"""
import itertools


def check(k, T, parts, PI):
    V = [(j, i) for j, v in enumerate(parts) for i in range(v)]; N = len(V); c = N - k
    prof = lambda K: tuple(sum(1 for x in K if x[0] == j) for j in range(len(parts)))
    fam = [frozenset(K) for K in itertools.combinations(V, c) if prof(K) in PI]
    famset = set(fam)
    assert all(any(set(S) <= K for K in fam) for S in itertools.combinations(V, T)), "not T-covering"
    pi = next(p for p in sorted(PI) if all(3 * p[j] >= parts[j] and (3 * p[j] - parts[j]) % 2 == 0 for j in range(len(parts))))
    kap = [(3 * pi[j] - parts[j]) for j in range(len(parts))]; assert all(x % 2 == 0 for x in kap)
    kappa = [(j, i) for j in range(len(parts)) for i in range(kap[j] // 2)]
    rest = {j: [(j, i) for i in range(kap[j] // 2, parts[j])] for j in range(len(parts))}
    pet = [[], [], []]
    for j in rest:
        m = len(rest[j]) // 3
        for r in range(3): pet[r] += rest[j][r * m:(r + 1) * m]
    Ks = [frozenset(kappa + pet[r]) for r in range(3)]
    assert all(K in famset for K in Ks) and len(kappa) == N - 3 * k // 2
    half = [(p[:len(p) // 2], p[len(p) // 2:]) for p in pet]
    lines = [half[0][a] + half[1][b] + half[2][a ^ b] for a in (0, 1) for b in (0, 1)]
    assert all(len(L) <= T for L in lines)
    opts = [[K for K in fam if set(L) <= K] for L in lines]
    bad = 0; tot = 0
    for ch in itertools.product(*opts):
        seven = Ks + list(ch); tot += 1
        if not all(any(x in K and y in K for K in seven) for x, y in itertools.combinations_with_replacement(V, 2)): bad += 1
    print(f"k={k} T={T} N={N} parts={parts} PI={PI}: |family|={len(fam)}, pencil profile {pi}, reply choices {tot}, failures {bad}")


check(4, 3, (5, 3), {(3, 1), (1, 3)})
check(4, 3, (5, 3), {(3, 1), (2, 2), (1, 3)})
check(4, 3, (4, 4), {(2, 2), (4, 0), (0, 4)})
check(4, 3, (3, 3, 2), {(1, 1, 2), (3, 1, 0), (1, 3, 0), (2, 1, 1), (1, 2, 1), (2, 2, 0)})
