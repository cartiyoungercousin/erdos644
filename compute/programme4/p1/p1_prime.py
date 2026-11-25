r"""P1' (PROGRAMME4_P1.md, Section 2): exact optimum of P1's colouring.
For a pencil with regions E_i, D_ij (Z -> p0), the four non-pencil lines have |L_g| = sums of one side of each class
C_1 = D23 + (E2,E3 parts), C_2 = D13 + (E1,E3 parts), C_3 = D12 + (E1,E2 parts).  Claim:
  min over E-assignments and splits of max_g |L_g| = ceil(|U|/2) + [stuck],
  stuck <=> every reachable class-parity pattern has exactly two odd classes.
Brute force over all region sizes <= M, all E-assignments, all splits.  usage: p1_prime.py M"""
import sys, itertools

def brute(e, d):
    e1, e2, e3 = e; d12, d13, d23 = d; best = 10 ** 9
    for a1 in range(e1 + 1):            # a1 points of E1 to C2, rest to C3
        for a2 in range(e2 + 1):        # E2 -> C1 (a2) / C3
            for a3 in range(e3 + 1):    # E3 -> C1 (a3) / C2
                c = (d23 + a2 + a3, d13 + a1 + (e3 - a3), d12 + (e1 - a1) + (e2 - a2))
                for al in itertools.product(*[range(ci + 1) for ci in c]):
                    be = [c[i] - al[i] for i in range(3)]
                    L = [al[0] + al[1] + al[2], al[0] + be[1] + be[2], be[0] + al[1] + be[2], be[0] + be[1] + al[2]]
                    best = min(best, max(L))
    return best

def formula(e, d):
    U = sum(e) + sum(d)
    p = ((d[2]) % 2, d[1] % 2, d[0] % 2)        # base parities of C1, C2, C3 with all E sent ... any base
    moves = []
    if e[2]: moves.append((1, 1, 0))            # an E3 point between C1 and C2
    if e[0]: moves.append((0, 1, 1))            # E1 between C2 and C3
    if e[1]: moves.append((1, 0, 1))            # E2 between C1 and C3
    # base assignment: E1 -> C3, E2 -> C3, E3 -> C2  (then add moves)
    base = ((d[2]) % 2, (d[1] + e[2]) % 2, (d[0] + e[0] + e[1]) % 2)
    reach = {base}
    for _ in range(3):
        reach |= {tuple((x + y) % 2 for x, y in zip(r, m)) for r in reach for m in moves}
    stuck = all(sum(r) == 2 for r in reach)
    return -(-U // 2) + (1 if stuck else 0)

if __name__ == '__main__':
    M = int(sys.argv[1]); n = bad = 0
    for e in itertools.product(range(M + 1), repeat=3):
        for d in itertools.product(range(M + 1), repeat=3):
            n += 1
            if brute(e, d) != formula(e, d): bad += 1; print('MISMATCH', e, d, brute(e, d), formula(e, d))
    print(f'{n} region-size vectors (all sizes <= {M}): {bad} mismatches')

def e2e(trials=300, seed=1):
    """End-to-end test of P1' on explicit families H_Z (T-covering, tau = T+1): for random pencils with
    w <= 4T-3k (non-stuck) or w <= 4T-3k-4 (stuck), build the optimal colouring, take a member of H_Z inside each R_g,
    and check by brute force that the seven has no transversal of size <= 2."""
    import random
    rng = random.Random(seed); done = 0
    LG = [(0,0,0),(0,1,1),(1,0,1),(1,1,0)]
    while done < trials:
        k = rng.randint(5, 14); T = rng.randint((3 * k) // 4 + 1, k - 1); q = 4 * T - 3 * k
        w = rng.randrange(k % 2, q + 1, 2) if q >= k % 2 else None
        if w is None: continue
        e = [0, 0, 0]
        for _ in range(w): e[rng.randrange(3)] += 1
        t = (3 * k - w) // 2; d23, d13, d12 = t - (k - e[0]), t - (k - e[1]), t - (k - e[2])
        if min(d12, d13, d23) < 0: continue
        U = (3 * k + w) // 2; stuck = formula(e, (d12, d13, d23)) > -(-U // 2)
        if stuck and w > q - 4: continue
        r = rng.randint(0, 3); n = k + T + r; z = n - U
        if z < r: continue
        # points: label regions
        pts = []; regs = [('E1', e[0], {0}), ('E2', e[1], {1}), ('E3', e[2], {2}), ('D12', d12, {0, 1}), ('D13', d13, {0, 2}), ('D23', d23, {1, 2})]
        for name, sz, ins in regs: pts += [(name, ins)] * sz
        xs = [set(i for i, p in enumerate(pts) if j in p[1]) for j in range(3)]
        # optimal colouring by brute force over E-assignments and splits (small)
        best = None
        for a1 in range(e[0] + 1):
            for a2 in range(e[1] + 1):
                for a3 in range(e[2] + 1):
                    cls = {}; cnt = {'E1': 0, 'E2': 0, 'E3': 0}
                    for i, (name, ins) in enumerate(pts):
                        if name == 'D23': cls[i] = 0
                        elif name == 'D13': cls[i] = 1
                        elif name == 'D12': cls[i] = 2
                        else:
                            c = cnt[name]; cnt[name] += 1
                            cls[i] = {'E1': (1 if c < a1 else 2), 'E2': (0 if c < a2 else 2), 'E3': (0 if c < a3 else 1)}[name]
                    C = [[i for i in cls if cls[i] == j] for j in range(3)]
                    for al in itertools.product(*[range(len(c) + 1) for c in C]):
                        bit = {}
                        for j in range(3):
                            for idx, i in enumerate(C[j]): bit[i] = 0 if idx < al[j] else 1
                        L = [set(i for i in cls if bit[i] == g[cls[i]]) for g in LG]
                        m = max(len(x) for x in L)
                        if best is None or m < best[0]: best = (m, L)
        m, L = best
        assert m <= T, (k, T, w, e, m)
        Zp = list(range(len(pts), n))
        seven = [x for x in xs]
        for Lg in L:
            Ru = [i for i in range(len(pts)) if i not in Lg]
            need = k - len(Ru)
            B = set(Ru[:k]) | set(Zp[:max(0, need)])
            assert len(B) == k and len(B & set(Zp)) <= z - r, 'R_g contains no member of H_Z'
            seven.append(B)
        for a in range(n):
            for b in range(a, n):
                assert not all(a in B or b in B for B in seven), 'transversal'
        done += 1
    print(f'e2e: {trials} explicit P1-prime sevens in H_Z verified (no 2-point transversal)')

if __name__ == '__main__' and len(sys.argv) > 2:
    e2e(int(sys.argv[2]))
