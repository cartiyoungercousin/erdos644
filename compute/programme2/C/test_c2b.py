r"""Test of Theorem C2 (two-block families, PROGRAMME2_C.md) and of the pencil lemma P1 that it uses.
For random (k, n, a, J) with tau(H_J) >= 3k/4 + 3 and 3k/2 <= n < 9k/4:
 (i) if J meets the window [k - 2b/3, 2a/3], build three j-profile members with empty triple intersection and
     wt(B1+B2+B3) <= 2, colour by the proof of P1, pick members inside the other four R_l, and brute-force check
     that the seven have no 2-point transversal;
 (ii) otherwise assert tau <= n/3 + 2 (which contradicts tau >= 3k/4 + 3), i.e. case (ii) never occurs.
Also cross-checks with the ILP of twoblock.seven on a subsample.  usage: test_c2b.py trials seed"""
import sys, random, math
from twoblock import tau, seven, LINES

PAIRS = [(4, 5), (6, 2), (1, 3)]      # lines through 0 are {0} + pair (LINES[4], LINES[6], LINES[0])

def triple(pts, j):
    """three j-subsets of pts with empty triple intersection, every point in <= 2, once-covered count (3j mod 2)."""
    if j % 2 == 0: d = [j // 2] * 3; e = 0          # d = (d12, d13, d23)
    else: d = [(j - 1) // 2, (j - 1) // 2, (j + 1) // 2]; e = 1
    assert sum(d) + e <= len(pts)
    it = iter(pts); D = [[next(it) for _ in range(c)] for c in d]; E = [next(it) for _ in range(e)]
    B1 = set(D[0] + D[1] + E); B2 = set(D[0] + D[2]); B3 = set(D[1] + D[2])
    assert len(B1) == len(B2) == len(B3) == j and not (B1 & B2 & B3)
    return [B1, B2, B3]

def check(k, a, b, J, R):
    n = a + b; t = tau(J, a, b, k)
    lo, hi = k - 2 * b / 3, 2 * a / 3
    js = [j for j in J if lo <= j <= hi]
    if not js:
        assert t <= n / 3 + 2, ('case ii violated', k, a, b, J, t); return 'ii'
    j = js[0]
    X = list(range(a)); Y = list(range(a, n))
    TX = triple(X, j); TY = triple(Y, k - j)
    B = [TX[i] | TY[i] for i in range(3)]
    w = len(B[0] ^ B[1] ^ B[2]); assert w <= 2 and not (B[0] & B[1] & B[2])
    col = {}; dest = [[], [], []]
    for v in range(n):
        ins = [i for i in range(3) if v in B[i]]
        if not ins: col[v] = 0
        elif len(ins) == 2: dest[3 - sum(ins)].append(v)          # D_ij -> pair Q_k
        else: dest[(ins[0] + 1) % 3].append(v)                    # E_i -> pair Q_{i+1}
    for i in range(3):
        for idx, v in enumerate(dest[i]): col[v] = PAIRS[i][idx % 2]
    sev = []
    for L in LINES:
        Rl = [v for v in range(n) if col[v] not in L]
        if 0 in L:
            i = next(i for i in range(3) if set(PAIRS[i]) <= set(L)); Bl = B[i]
            assert Bl <= set(Rl)
        else:
            RX = [v for v in Rl if v < a]; RY = [v for v in Rl if v >= a]
            jj = next((jj for jj in J if jj <= len(RX) and 0 <= k - jj <= len(RY)), None)
            assert jj is not None, ('no member in R_l', k, a, b, J, t, len(Rl), n - t + 1)
            Bl = set(RX[:jj] + RY[:k - jj])
        sev.append(Bl)
    for u in range(n):
        for x in range(u, n):
            assert not all(u in S or x in S for S in sev), 'two-point transversal'
    return 'i'

if __name__ == '__main__':
    trials, seed = int(sys.argv[1]), int(sys.argv[2]); R = random.Random(seed)
    from collections import Counter
    cnt = Counter(); ilp = 0
    while sum(cnt.values()) < trials:
        k = R.randint(8, 40); n = R.randint(math.ceil(3 * k / 2), math.ceil(9 * k / 4) - 1); a = R.randint(1, n - 1); b = n - a
        rng = list(range(max(0, k - b), min(a, k) + 1)); p = R.choice([0.3, 0.5, 0.8, 0.95])
        J = sorted(j for j in rng if R.random() < p)
        if not J or tau(J, a, b, k) < 3 * k / 4 + 3: cnt['skip'] += 0; continue
        cnt[check(k, a, b, J, R)] += 1
        if ilp < 40 and n <= 60:
            assert seven(J, a, b, k) is not None; ilp += 1
    print(dict(cnt), 'ILP cross-checks', ilp)
