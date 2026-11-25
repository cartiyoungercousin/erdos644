"""Exact check of the TWO-STAGE centred dump (PROGRAMME5_BULK Theorem 2S), all integers.
Setting: H k-uniform, (k+r)-covering on n = k+r+T points. w = ceil((r-1)/2); I* = {hi*-w..hi*} the block of w+1
consecutive integers minimising D = max_{j in I*} |2j-(k-r)| (lower block on a tie), as in the paper.
Strategy: start pair with s = hi* points of x1 (j in [max(0,hi*-r), hi*]); intermediate dump with block
[hi'-w, hi'], hi' = k-hi*; final dump with block I*; pair bound -> pencil of weight <= r + D.
Checks, for every k <= K, r >= 3, T >= 0 with 4T >= 2k+3r+3 (and T <= k-1, else tau >= k+1 > n-k+1... kept anyway):
 (S) start: 0 <= s <= k-1 and k+r-s <= n-k.
 (M) for every start j: j <= k-hi', 0 <= k+r-2hi' <= n-2k+j, and the output block [max(0,hi'-w), hi'] lies in
     G = { j' : j' <= k-hi*, 0 <= k+r-2hi* <= n-2k+j' }   (final-dump admissible states), and hi' <= k-1.
 (F) hi* <= T (pair bound needs j'' <= T), hi* >= 0, r + D <= floor(3r/2)+1.
Also: the 3/11 corollary range  11T >= 3n+3k+11, n <= (8k+11)/3  =>  4T >= 2k+3r+3 (or r <= 2 handled by the
paper's own conditions)."""
import sys, math

def block(k, r):
    w = max(0, math.ceil((r - 1) / 2))
    best = None
    for hi in range(-2 * k, 2 * k + 1):   # paper's choice: minimise the UNCLIPPED D, lower block on a tie
        D = max(abs(2 * j - (k - r)) for j in (hi - w, hi))
        if best is None or D < best[0]: best = (D, hi)
    hi = best[1]
    Dc = max(abs(2 * j - (k - r)) for j in (max(0, hi - w), hi))   # answers are >= 0: clipped block
    return w, hi, Dc

def check(K):
    bad = 0; cases = 0
    for k in range(4, K + 1):
        for r in range(3, 2 * k + 1):
            w, hs, D = block(k, r)
            for T in range(0, 2 * k):
                if 4 * T < 2 * k + 3 * r + 3: continue
                n = k + r + T; cases += 1
                ok = True
                s = hs; hp = k - hs
                ok &= 0 <= s <= k - 1 and k + r - s <= n - k
                for j in range(max(0, s - r), s + 1):
                    ok &= j <= k - hp and 0 <= k + r - 2 * hp <= n - 2 * k + j
                ok &= hp <= k - 1
                for jp in range(max(0, hp - w), hp + 1):
                    ok &= jp <= k - hs and 0 <= k + r - 2 * hs <= n - 2 * k + jp
                ok &= 0 <= hs <= T and r + D <= (3 * r) // 2 + 1
                if not ok:
                    bad += 1
                    if bad <= 10: print('FAIL k=%d r=%d T=%d hi*=%d w=%d' % (k, r, T, hs, w))
    print('two-stage conditions: %d cases, %d failures' % (cases, bad))
    # range of the 3/11 corollary
    bad2 = 0; c2 = 0
    for k in range(4, K + 1):
        for n in range(k, (8 * k + 11) // 3 + 1):
            for T in range(0, n - k + 1):
                if 11 * T < 3 * n + 3 * k + 11: continue
                r = n - k - T; c2 += 1
                if r >= 3 and 4 * T < 2 * k + 3 * r + 3: bad2 += 1
                if r <= 2 and not (4 * T >= 2 * k + 5 * r + 3 and 3 * r <= 2 * k - 2): bad2 += 1
    print('3/11 range n <= (8k+11)/3: %d (n,k,T) above the line, %d not covered by a pencil theorem' % (c2, bad2))

if __name__ == '__main__':
    check(int(sys.argv[1]))
