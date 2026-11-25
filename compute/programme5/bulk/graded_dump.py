"""Graded (iterated) centred dump: the pencil bound with the dump block chosen AFTER the pair is seen.
Exact integer game, all n. H k-uniform, (k+r)-covering on n points, T = n-k-r.
State j = |x1 cap x2| of the current pair (distinct members, j <= k-1).
 * stop:  pair bound (paper Lemma pair): a pencil of weight <= r + |k-r-2j|, valid if j <= T.
 * dump:  choose hi, w with 2w+2 > r, j <= k-hi, 0 <= k+r-2hi <= n-2k+j (paper Lemma dump, A_i of size hi in
          x_i - x_{3-i}, O outside x1 u x2); the adversary answers some y with j' = |y cap x_i| in [max(0,hi-w), hi].
 * start: x1 any, S = s points of x1 + (k+r-s) outside (needs k+r-s <= n-k, s <= k-1): j in [max(0,s-r), s].
W(n,k,r) = min_s max_j V(j), V = value of the game (min over moves, max over answers).
Seven-free => W(n,k,tau-1-dependent r) >= 4T-3k-5 (Lemma P1), giving tau <= 1 + max{T : W >= 4T-3k-5}.
usage: py -3.14 graded_dump.py k [nu_min nu_max steps]"""
import sys, math
INF = 10 ** 9

def W(n, k, r):
    T = n - k - r
    if T < 0: return INF
    w = max(0, math.ceil((r - 1) / 2))
    term = [(r + abs(k - r - 2 * j)) if j <= T else INF for j in range(k)]
    V = term[:]
    for it in range(60):
        # best dump value from state j: min over hi of max V on [max(0,hi-w), hi]
        # window max via simple loop with precomputation per hi
        win = [max(V[max(0, hi - w):hi + 1]) for hi in range(k)]
        new = V[:]
        for j in range(k):
            # hi constraints: hi <= k-j, 2hi <= k+r, 2hi >= k+r-(n-2k+j), hi <= k-1
            lo_hi = max(0, math.ceil((k + r - (n - 2 * k + j)) / 2))
            up_hi = min(k - j, (k + r) // 2, k - 1)
            if lo_hi <= up_hi:
                b = min(win[lo_hi:up_hi + 1])
                if b < new[j]: new[j] = b
        if new == V: break
        V = new
    best = INF
    for s in range(max(0, 2 * k + r - n), k):
        m = max(V[max(0, s - r):s + 1])
        best = min(best, m)
    return best

def tau_bound(n, k):
    """largest tau consistent with seven-freeness by this argument (tau <= n-k+1 always)."""
    # T above the NC bound (2n+k+11)/6 - 1 is already excluded (paper eq. NCV); scan down from just above it
    for T in range(min(n - k, (2 * n + k + 11) // 6 + 2), -1, -1):
        r = n - k - T
        if W(n, k, r) >= 4 * T - 3 * k - 5:
            return T + 1
    return 0

if __name__ == '__main__':
    k = int(sys.argv[1])
    a, b, st = (float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])) if len(sys.argv) > 4 else (1.75, 2.4, 26)
    print('k=%d' % k)
    print(' nu      n   tau_bd  eps=(tau-3k/4)/k  NC(2n+k+11)/6  3/11-line  sigma/3-1/42  FKW 7k/8')
    for i in range(st + 1):
        nu = a + (b - a) * i / st
        n = round(nu * k)
        tb = tau_bound(n, k)
        s = n - 7 * k / 4
        print('%.4f %5d %6d   %.5f          %8.2f      %8.2f   %8.2f   %6.1f' % (
            n / k, n, tb, (tb - 3 * k / 4) / k, (2 * n + k + 11) / 6, (3 * n + 3 * k + 21) / 11,
            3 * k / 4 + s / 3 - k / 42, math.ceil(7 * k / 8)), flush=True)
