"""Bottom strip (CORE §90-§94): exact finite-k check of the pair certificate (CORE 77.1).

Two co-edges K_0, K_1 (|K| = n - k) of an n-set with |K_0 ∩ K_1| = o.  Replies are labelled by
Fano points 0..6, classes by lines.  ILP (exact, integers): assign every point of the four cells
O = K_0∩K_1, A = K_0∖K_1, B = K_1∖K_0, G = V∖(K_0∪K_1) to a line compatible with its co-type so far;
the five requests L_j (j = 2..6, union of the classes on lines through j) must have size <= T.
Then (exact) build the seven co-edges as real sets, pad L_j adversarially/randomly to size n - k, and
check by brute force that every pair of points lies in a common co-edge (CORE 1.1).

usage: py pair_window.py k T n [trials]
prints the exact integer window Z_k = {o : feasible} and the first-order prediction [n-2T, 3T-2k].
"""
import sys, random, itertools
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__file__), "..", "core8"))
from lpx import LP, INF

LINES = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
CELLS = {'O': {0, 1}, 'A': {0}, 'B': {1}, 'G': set()}


def solve(k, T, n, o):
    c = n - k
    size = {'O': o, 'A': c - o, 'B': c - o, 'G': n - 2 * c + o}
    if min(size.values()) < 0:
        return None
    lp = LP()
    x = {}
    for cell, P in CELLS.items():
        for li, L in enumerate(LINES):
            if set(L) & {0, 1} <= P:
                x[cell, li] = lp.var(integer=True)
    for cell in CELLS:
        lp.row([(v, 1.0) for (cc, li), v in x.items() if cc == cell], size[cell], size[cell])
    for j in range(2, 7):
        lp.row([(v, 1.0) for (cc, li), v in x.items() if j in LINES[li]], -INF, T)
    val, sol = lp.solve()
    if sol is None:
        return None
    return {key: int(round(sol[v])) for key, v in x.items()}, size


def build_and_check(k, T, n, o, sol, size, trials, rng):
    c = n - k
    # points 0..n-1: O, A, B, G in order
    pts, cls = [], {}
    cur = 0
    cellpts = {}
    for cell in 'OABG':
        cellpts[cell] = list(range(cur, cur + size[cell]))
        cur += size[cell]
    assert cur == n
    line_of = {}
    for cell in 'OABG':
        it = iter(cellpts[cell])
        for li in range(7):
            for _ in range(sol.get((cell, li), 0)):
                line_of[next(it)] = li
    assert len(line_of) == n
    K0 = set(cellpts['O'] + cellpts['A'])
    K1 = set(cellpts['O'] + cellpts['B'])
    req = {j: {p for p in range(n) if j in LINES[line_of[p]]} for j in range(2, 7)}
    assert all(len(req[j]) <= T for j in req)
    for j in req:  # her requests are legal: confined game, request inside V, size <= T
        pass
    fails = 0
    for tr in range(trials):
        Ks = [K0, K1]
        for j in range(2, 7):
            rest = [p for p in range(n) if p not in req[j]]
            if tr % 3 == 0:
                rng.shuffle(rest)
            elif tr % 3 == 1:   # adversarial-ish: pad with points whose class line avoids j, low line index first
                rest.sort(key=lambda p: (LINES[line_of[p]][0], rng.random()))
            else:
                rest.sort(key=lambda p: (-len(set(LINES[line_of[p]]) & set(range(j))), rng.random()))
            Ks.append(req[j] | set(rest[:c - len(req[j])]))
        assert all(len(K) == c for K in Ks)
        I = [frozenset(i for i in range(7) if p in Ks[i]) for p in range(n)]
        ok = all(I[p] for p in range(n)) and all(I[p] & I[q] for p, q in itertools.combinations(range(n), 2))
        fails += (not ok)
    return fails


def main():
    k, T, n = map(int, sys.argv[1:4])
    trials = int(sys.argv[4]) if len(sys.argv) > 4 else 30
    rng = random.Random(1)
    c = n - k
    Z, totfail = [], 0
    for o in range(0, c + 1):
        r = solve(k, T, n, o)
        if r is None:
            continue
        sol, size = r
        f = build_and_check(k, T, n, o, sol, size, trials, rng)
        totfail += f
        Z.append(o)
    print(f'k={k} T={T} n={n}: exact window Z_k = {Z}  first-order [n-2T, 3T-2k] = [{n-2*T}, {3*T-2*k}]'
          f'  brute-force failures over {trials} paddings per o: {totfail}')


if __name__ == '__main__':
    main()
