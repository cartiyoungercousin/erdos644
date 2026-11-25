"""Explicit end-to-end test of the Lemma P1 colouring (own code).
Random pencil triples x1,x2,x3 (k-sets, empty triple intersection) in [n]; build the colouring
Z->p0, D_ij->Q_k, E_i->Q_{i+1}, each Q_i class split evenly; check x_i subset R_{l_i},
check min |R_l| over the other 4 lines >= n - (3k+w)/4 - 3/2 and, whenever w <= 4T-3k-6, >= n-T;
then pick arbitrary k-subsets B_l of R_l for the other 4 lines and brute-force check that the 7 sets
have no 2-point transversal.   usage: p1_check.py trials seed"""
import sys, random, itertools
trials, seed = int(sys.argv[1]), int(sys.argv[2]); rnd = random.Random(seed)
# Fano points 0..6, p0 = 0; lines through 0: {0,1,2},{0,3,4},{0,5,6}  => Q1={1,2},Q2={3,4},Q3={5,6}
LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
Q = {1: (1, 2), 2: (3, 4), 3: (5, 6)}
bad = 0; tested = 0; trig = 0
for _ in range(trials):
    k = rnd.randint(2, 14); n = rnd.randint(3 * k // 2 + 1, 3 * k + 2)
    V = list(range(n))
    while True:
        xs = [set(rnd.sample(V, k)) for _ in range(3)]
        if not (xs[0] & xs[1] & xs[2]): break
    U = xs[0] | xs[1] | xs[2]; w = sum(1 for v in V if sum(v in x for x in xs) == 1)
    col = {}
    cls = {1: [], 2: [], 3: []}
    for v in V:
        mem = tuple(i for i in range(3) if v in xs[i])
        if not mem: col[v] = 0
        elif len(mem) == 1: cls[(mem[0] + 1) % 3 + 1].append(v)          # E_i -> Q_{i+1}
        else: cls[({0, 1, 2} - set(mem)).pop() + 1].append(v)            # D_ij -> Q_k
    for i in (1, 2, 3):
        for t, v in enumerate(cls[i]): col[v] = Q[i][t % 2]
    R = [set(v for v in V if col[v] not in L) for L in LINES]
    tested += 1
    ok = all(xs[i] <= R[i] for i in range(3))
    minR = min(len(R[l]) for l in range(3, 7))
    ok &= minR >= n - (3 * k + w) / 4 - 1.5
    # pick T: largest T with w <= 4T-3k-6, i.e. T = ceil((w+3k+6)/4); check minR >= n-T
    T = -(-(w + 3 * k + 6) // 4)
    if T <= n - k:
        trig += 1; ok &= minR >= n - T
    if all(len(R[l]) >= k for l in range(3, 7)):
        Bs = [xs[0], xs[1], xs[2]] + [set(rnd.sample(sorted(R[l]), k)) for l in range(3, 7)]
        for p, q in itertools.combinations_with_replacement(V, 2):
            if all((p in B) or (q in B) for B in Bs): ok = False; break
    if not ok: bad += 1; print('FAIL', k, n, w)
print(f"trials={tested} with P1 threshold reachable={trig} failures={bad}")
