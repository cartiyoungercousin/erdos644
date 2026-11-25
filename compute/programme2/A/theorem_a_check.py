r"""Programme 2, piece A: exact randomized check of Theorems A1 (split colouring) and A2 (one heavy colour).
For each instance H (nonempty sets on n <= 11 points) and each feasible y (y(M) >= 1 on every transversal,
checked exactly in Fractions) and each threshold set A = {y >= theta}:
  A1: if some <=3 members of H_A = {B : B cap A = empty} have empty common intersection and
      Lam + 3a' < 2   (Lam = y(V-A), a' = max y on V-A),
  A2: if Lam + 3a' >= 2 and y(V) + 7a' < 7/3,
then the explicit construction of the notes yields a Fano colouring with no transversal line; the 7 members
are extracted and checked by brute force to have no transversal of <= 2 points.  Any failure is printed.
Usage: py -3.14 theorem_a_check.py [trials] [seed]"""
import itertools, random, sys
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog

LINES = [(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
PAIRS = [(1,3),(4,5),(6,2)]        # the lines through colour 0 are {0}+pair

def transversals(n, H):
    return [M for M in range(1 << n) if all(M & B for B in H)]

def min_transversals(n, H):
    T = transversals(n, H); Ts = set(T)
    return [M for M in T if not any((M & ~(1 << i)) in Ts for i in range(n) if M >> i & 1)]

def wt(y, M):
    return sum((y[i] for i in range(len(y)) if M >> i & 1), F(0))

def feasible(y, mins):
    return all(wt(y, M) >= 1 for M in mins)

def lp_y(n, mins):
    A = np.array([[-(M >> i & 1) for i in range(n)] for M in mins], float)
    r = linprog(np.ones(n), A_ub=A, b_ub=-np.ones(len(mins)), bounds=[(0, None)] * n, method='highs')
    y = [F(v).limit_denominator(1000) for v in r.x]
    while not feasible(y, mins):           # rational repair: scale up
        y = [v * F(1001, 1000) for v in y]
    return y

def is_72_witness(n, seven):
    for a in range(n):
        for b in range(a, n):
            X = (1 << a) | (1 << b)
            if all(X & B for B in seven): return False
    return True

def seven_from_colouring(H, col):
    seven = []
    for ln in LINES:
        L = sum(1 << v for v, c in col.items() if c in ln)
        Bs = [B for B in H if not (B & L)]
        if not Bs: return None
        seven.append(Bs[0])
    return seven

def halve(pts, y):
    a, b, wa, wb = [], [], F(0), F(0)
    for v in sorted(pts, key=lambda v: -y[v]):
        if wa <= wb: a.append(v); wa += y[v]
        else: b.append(v); wb += y[v]
    return a, b

def construct_A1(n, H, y, A):
    HA = [B for B in H if not (B & A)]
    trip = None
    for r in (1, 2, 3):
        for c in itertools.combinations(HA, r):
            if (c[0] & c[-1] & c[len(c) // 2]) == 0 if r == 3 else (r == 2 and (c[0] & c[1]) == 0):
                trip = list(c) + [c[0]] * (3 - r); break
        if trip: break
    if trip is None: return 'nohyp', None
    col = {v: 0 for v in range(n) if A >> v & 1}
    X = [[], [], []]
    for v in range(n):
        if A >> v & 1: continue
        s = next(i for i in range(3) if not (trip[i] >> v & 1))
        X[s].append(v)
    for s in range(3):
        h1, h2 = halve(X[s], y)
        for v in h1: col[v] = PAIRS[s][0]
        for v in h2: col[v] = PAIRS[s][1]
    return 'ok', col

def construct_A2(n, y, A, ap):
    Lam = sum((y[v] for v in range(n) if not A >> v & 1), F(0))
    sigma = F(1, 10**6) * (1 - 0)        # tiny
    s = (1 - 3 * ap) / 3 - sigma
    t = Lam - 6 * s
    assert t >= 0
    target = [t] + [s] * 6
    col = {v: 0 for v in range(n) if A >> v & 1}
    load = [F(0)] * 7; q = 0
    for v in [v for v in range(n) if not A >> v & 1]:
        while q < 6 and load[q] >= target[q]: q += 1
        col[v] = q; load[q] += y[v]
    return col

def check_instance(n, H, y, stats, tag):
    V = [v for v in range(n) if any(B >> v & 1 for B in H)]
    yV = sum(y, F(0))
    for th in sorted(set(y) | {F(10**6)}):
        A = sum(1 << v for v in range(n) if y[v] >= th)
        light = [y[v] for v in range(n) if not A >> v & 1]
        Lam = sum(light, F(0)); ap = max(light, default=F(0))
        todo = []
        if Lam + 3 * ap < 2:
            st, col = construct_A1(n, H, y, A)
            if st == 'ok': todo.append(('A1', col))
        elif yV + 7 * ap < F(7, 3):
            todo.append(('A2', construct_A2(n, y, A, ap)))
        for kind, col in todo:
            stats[kind] += 1
            seven = seven_from_colouring(H, col)
            if seven is None or not is_72_witness(n, seven):
                stats['FAIL'] += 1; print('FAIL', kind, tag, n, H, y, A)

def rand_family(rng):
    n = rng.randint(4, 11); kind = rng.random()
    if kind < 0.3:        # dense subfamily of a complete family (rich when n/(n-k+1) is small)
        n = rng.randint(6, 12); k = rng.randint(2, max(2, n // 2))
        H = [sum(1 << v for v in c) for c in itertools.combinations(range(n), k) if rng.random() < rng.uniform(0.5, 1)]
    elif kind < 0.55:     # random family with sizes <= k
        k = rng.randint(2, n - 1)
        H = [sum(1 << v for v in rng.sample(range(n), rng.randint(1, k))) for _ in range(rng.randint(3, 60))]
    elif kind < 0.8:      # H1 + one singleton {b} (forced heavy atom)
        k = rng.randint(2, n - 2)
        H = [sum(1 << v for v in rng.sample(range(n - 1), rng.randint(1, k))) for _ in range(rng.randint(3, 40))]
        H.append(1 << (n - 1))
    else:                 # H1 + star at b (heavy point with petals)
        k = rng.randint(2, n - 2); b = n - 1
        H = [sum(1 << v for v in rng.sample(range(n - 1), rng.randint(1, k))) for _ in range(rng.randint(3, 30))]
        H += [(1 << b) | sum(1 << v for v in rng.sample(range(n - 1), rng.randint(0, k - 1))) for _ in range(rng.randint(1, 20))]
    H = sorted(set(h for h in H if h))
    return n, H

def main():
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    stats = {'inst': 0, 'A1': 0, 'A2': 0, 'FAIL': 0}
    for it in range(trials):
        n, H = rand_family(rng)
        if not H: continue
        mins = min_transversals(n, H)
        y0 = lp_y(n, mins)
        ys = [y0]
        for _ in range(3):   # perturbed feasible y (add random light/heavy extra mass)
            ys.append([v + F(rng.randint(0, 3), rng.randint(20, 200)) * (rng.random() < 0.4) for v in y0])
        for y in ys:
            assert feasible(y, mins)
            check_instance(n, H, y, stats, it)
        stats['inst'] += 1
    print(stats)

if __name__ == '__main__':
    main()
