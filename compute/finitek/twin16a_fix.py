"""Finite-k Theorem C (TWIN 13.4) and Proposition 16.A (TWIN 16.3), with the kernel enlarged by one.
Part 1: integer Theorem C: three anchors with disjoint pairwise parts, |union| = U <= 2T-1  =>  four requests, each <= T,
        satisfying all Theorem-B conditions (exhaustive over part sizes).  U = 2T is tested too (exact criterion in FINITE_K.md).
Part 2: end-to-end 16.A: seven requests, adversary random / overlap-maximising; final seven checked for a 2-cover over all of V.
Usage: py -3.14 twin16a_fix.py [part1_Tmax] [kmax] [plays]
"""
import sys, random, itertools, math

# requests {4,5,6,7} = vertices of K4; matchings M1={47,56} (P12), M2={46,57} (P13), M3={45,67} (P23).
# A point's type is an edge (the two requests containing it).  Load of request i = number of points on edges at i.
M = [((4, 7), (5, 6)), ((4, 6), (5, 7)), ((4, 5), (6, 7))]


def split_sizes(sizes):
    """sizes = (a,b,c,q1,q2,q3) = (|P12|,|P13|,|P23|,|Q1|,|Q2|,|Q3|).
    Routing: Q1 -> M1 (allowed: not a type of the opposite P23=M3), Q3 -> M2 (opposite P12=M1), Q2 -> M3 (opposite P13=M2).
    W_j = total mass on matching j.  Odd W_j gets offset e_j = +-1 (x_j = (W_j+e_j)/2 on the first edge, y_j on the second)."""
    a, b, c, q1, q2, q3 = sizes
    W = [a + q1, b + q3, c + q2]
    odd = [j for j in range(3) if W[j] % 2]
    best = None
    for es in itertools.product((1, -1), repeat=len(odd)):
        e = [0, 0, 0]
        for j, s in zip(odd, es):
            e[j] = s
        x = [(W[j] + e[j]) // 2 for j in range(3)]
        y = [(W[j] - e[j]) // 2 for j in range(3)]
        mx = max(loads(x, y).values())
        if best is None or mx < best[0]:
            best = (mx, x, y)
    return best[0], best[1], best[2], W


def loads(x, y):
    return {4: x[0] + x[1] + x[2], 5: y[0] + y[1] + x[2], 6: y[0] + x[1] + y[2], 7: x[0] + y[1] + y[2]}


def theorem_B_check(sizes, x, y):
    """explicit groups (set label, type, count); every pair required by Theorem B must have intersecting types."""
    a, b, c, q1, q2, q3 = sizes
    P = (a, b, c)
    Qlab = {0: 1, 1: 3, 2: 2}      # matching j carries Q_{Qlab[j]}
    groups = []
    for j in range(3):
        p1 = min(P[j], x[j]); p2 = P[j] - p1
        assert p2 <= y[j]
        groups.append((('P', j), frozenset(M[j][0]), p1))
        groups.append((('P', j), frozenset(M[j][1]), p2))
        groups.append((('Q', Qlab[j]), frozenset(M[j][0]), x[j] - p1))
        groups.append((('Q', Qlab[j]), frozenset(M[j][1]), y[j] - p2))
    opp = {0: 3, 1: 2, 2: 1}       # P12 <-> Q3, P13 <-> Q2, P23 <-> Q1
    for (kx, tx, nx) in groups:
        if kx[0] != 'P' or nx == 0:
            continue
        for (ky, ty, ny) in groups:
            if ny == 0:
                continue
            need = (ky[0] == 'P' and ky[1] != kx[1]) or (ky[0] == 'Q' and ky[1] == opp[kx[1]])
            if need and not (tx & ty):
                return False
    return True


def part1(Tmax):
    cases = bad = tightok = tightfail = 0
    for T in range(1, Tmax + 1):
        for sizes in itertools.product(range(0, 2 * T + 1), repeat=6):
            U = sum(sizes)
            if U > 2 * T:
                continue
            mx, x, y, W = split_sizes(sizes)
            if U <= 2 * T - 1:
                cases += 1
                if mx > T or not theorem_B_check(sizes, x, y):
                    bad += 1
                    print("FAIL", T, sizes)
            else:
                if mx <= T:
                    tightok += 1
                else:
                    tightfail += 1
    print(f"Part 1 (T<={Tmax}): {cases} part-size vectors with U<=2T-1: loads<=T and Theorem B conditions hold in {cases - bad}, failures {bad}")
    print(f"           U=2T with the fixed Q-routing: load<=T in {tightok}, load>T in {tightfail}")


def play(k, T, N, rnd, mode):
    V = list(range(N))
    rnd.shuffle(V)
    B1 = set(V[:k])
    out = V[k:]
    al = max(0, N - 2 * T + 1)
    a0 = set(rnd.sample(out, al))
    take = min(k, T - al)
    S2 = a0 | set(rnd.sample(sorted(B1), take))
    assert len(S2) <= T
    free2 = [v for v in V if v not in S2]
    if mode == 'maxov':
        pref = [v for v in free2 if v in B1] + [v for v in free2 if v not in B1]
        B2 = set(pref[:k])
    else:
        B2 = set(rnd.sample(free2, k))
    S3 = a0 | (B1 & B2)
    assert len(S3) <= T, (len(S3), T)
    free3 = [v for v in V if v not in S3]
    if mode == 'maxov':
        pref = [v for v in free3 if v in B1 or v in B2]
        rest = [v for v in free3 if v not in B1 and v not in B2]
        rnd.shuffle(pref)
        B3 = set((pref + rest)[:k])
    else:
        B3 = set(rnd.sample(free3, k))
    assert not (B1 & B2 & B3)
    Uset = B1 | B2 | B3
    assert not (Uset & a0)
    P12 = B1 & B2
    P13 = B1 & B3
    P23 = B2 & B3
    Q1 = B1 - B2 - B3
    Q2 = B2 - B1 - B3
    Q3 = B3 - B1 - B2
    sizes = tuple(len(s) for s in (P12, P13, P23, Q1, Q2, Q3))
    U = sum(sizes)
    assert U == len(Uset) and U <= 2 * T - 1, (U, T)
    mx, x, y, W = split_sizes(sizes)
    assert mx <= T
    reqs = {4: set(), 5: set(), 6: set(), 7: set()}
    for j, (Pj, Qs) in enumerate(((P12, Q1), (P13, Q3), (P23, Q2))):
        pts = sorted(Pj) + sorted(Qs)
        for idx, pnt in enumerate(pts):
            e = M[j][0] if idx < x[j] else M[j][1]
            for r in e:
                reqs[r].add(pnt)
    Ss = [S2, S3] + [reqs[r] for r in (4, 5, 6, 7)]
    assert all(len(s) <= T for s in Ss), [len(s) for s in Ss]
    reps = [B1, B2, B3]
    for s in Ss[2:]:
        fr = [v for v in V if v not in s]
        rnd.shuffle(fr)
        reps.append(set(fr[:k]))
    cov = [0] * N
    for j, B in enumerate(reps):
        for v in B:
            cov[v] |= 1 << j
    full = (1 << 7) - 1
    for i in range(N):
        for j in range(i, N):
            if cov[i] | cov[j] == full:
                return False
    return True


def part2(kmax, plays):
    rnd = random.Random(11)
    tot = bad = insts = 0
    for k in range(1, kmax + 1):
        for T in range(math.ceil(3 * k / 4), k + 3):
            for N in range(k + T, 3 * T + 1):
                if 2 * N > 6 * T - k - 2:
                    continue            # N <= 3T - k/2 - 1
                insts += 1
                for p in range(plays):
                    tot += 1
                    if not play(k, T, N, rnd, 'maxov' if p % 2 else 'rand'):
                        bad += 1
                        print("FAIL16A", k, T, N)
    print(f"Part 2: {insts} (k,T,N) with 4T>=3k, k+T<=N<=3T-k/2-1 ; {tot} plays ; 2-covers found: {bad}")


if __name__ == "__main__":
    Tm = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    km = int(sys.argv[2]) if len(sys.argv) > 2 else 14
    pl = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    part1(Tm)
    part2(km, pl)
