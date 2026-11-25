"""Exact integer check of the two-step covering argument for question (LT).

Setting: H k-uniform on n points, every (k+r)-set contains a member.
w = floor((12n-21k)/7): a triple is LIGHT if |x1+x2+x3| <= w (Lemma Q needs no light triple).
Pair lemma: if |x1 cap x2| = i lies in the band B = {i : k-w <= 2i <= k-2r+w}, a light triple exists.
Step-2 lemma: for i just above B, the set A2 = (x1 xor x2) + a points of x1&x2 + rest outside
forces every member x3 inside A2 to give a light triple or a pair (x1,x3)/(x2,x3) in B.
This script enumerates EVERY drop vector of the adversary (no closed form used) and reports
whether the forbidden set F = B u {step-2 wins} contains a window [l-r, l] reachable by covering.
Usage: py -3.14 lt_exact.py scan  |  py -3.14 lt_exact.py one n k r
"""
import sys
from math import ceil, floor


def band(n, k, r):
    w = (12 * n - 21 * k) // 7
    lo = -(-(k - w) // 2)            # ceil((k-w)/2)
    hi = (k - 2 * r + w) // 2        # floor((k-2r+w)/2)
    return w, lo, hi


def in_band(i, lo, hi):
    return lo <= i <= hi


def step2_wins(n, k, r, i, w, lo, hi):
    """True if some a makes every x3 inside A2 bad for the adversary (exhaustive over drops)."""
    s = 2 * k - 2 * i
    if s > k + r:
        return False, None
    m = k + r - s
    for a in range(0, min(i, m) + 1):
        if m - a > n - 2 * k + i or m - a < 0:
            continue
        survivor = None
        for al in range(0, min(a, r) + 1):
            for be in range(0, min(k - i, r - al) + 1):
                for ga in range(0, min(k - i, r - al - be) + 1):
                    th = r - al - be - ga
                    if th > m - a:
                        continue
                    # x3 = A2 minus drops; compute the three quantities from the atoms
                    p11, p10, p01, p00 = a - al, (k - i) - be, (k - i) - ga, (m - a) - th
                    assert p11 + p10 + p01 + p00 == k
                    W = p11 + ((k - i) - p10) + ((k - i) - p01) + p00   # |x1+x2+x3| atom by atom
                    i13, i23 = p11 + p10, p11 + p01
                    if W > w and not in_band(i13, lo, hi) and not in_band(i23, lo, hi):
                        survivor = (al, be, ga, th)
                        break
                if survivor:
                    break
            if survivor:
                break
        if survivor is None:
            return True, a
    return False, None


def analyse(n, k, r, verbose=False):
    w, lo, hi = band(n, k, r)
    if lo > hi:
        return dict(w=w, win=False, reason="empty band")
    F = set(range(lo, hi + 1))
    top = hi
    i = hi + 1
    while i < k:
        ok, a = step2_wins(n, k, r, i, w, lo, hi)
        if not ok:
            break
        F.add(i)
        top = i
        i += 1
    # window [l-r, l] inside F, with l <= k-1 and k+r-l <= n-k, l-r >= 0
    win = None
    for l in range(top, lo - 1, -1):
        if l - r >= lo and l <= k - 1 and k + r - l <= n - k:
            win = l
            break
    res = dict(w=w, band=(lo, hi), top=top, F_len=top - lo + 1, r=r, win=win is not None, l=win,
               margin=3 * w - 5 * r)
    if verbose:
        print(res)
    return res


if __name__ == "__main__":
    if sys.argv[1] == "one":
        n, k, r = map(int, sys.argv[2:5])
        analyse(n, k, r, verbose=True)
    elif sys.argv[1] == "scan":
        # all (n, k, r) with 7k/4 <= n < 11k/6, r >= 1, w >= r, for k in a range; record the
        # smallest margin 3w-5r at which the argument wins and the largest at which it fails
        kmin, kmax = int(sys.argv[2]), int(sys.argv[3])
        fail_max = -10**9
        win_min = 10**9
        bad = []
        cnt = 0
        for k in range(kmin, kmax + 1):
            for n in range(ceil(7 * k / 4), ceil(11 * k / 6)):
                w = (12 * n - 21 * k) // 7
                for r in range(1, w + 1):
                    res = analyse(n, k, r)
                    cnt += 1
                    mg = 3 * w - 5 * r
                    if res["win"]:
                        win_min = min(win_min, mg)
                    else:
                        fail_max = max(fail_max, mg)
                        if mg >= 0:
                            bad.append((n, k, r, w, mg))
        print(f"cases {cnt}; largest margin 3w-5r with NO win: {fail_max}; smallest margin with win: {win_min}")
        print("failures with margin >= 0 (first 20):", bad[:20], "count", len(bad))


def scan_routes(kmin, kmax, eps_list=(0.0, 0.005, 0.01, 0.02)):
    """Erdos-range scan: T = ceil((3/4+eps)k), n in [7k/4, 11k/6), r = n-k-T >= 0.
    Route A = two-step argument above; route B = Lemma 5c pencil bound (pen_check.best_interval) <= w."""
    from pen_check import best_interval
    tot = okA = okB = 0
    fails = []
    for k in range(kmin, kmax + 1):
        for eps in eps_list:
            T = ceil((0.75 + eps) * k)
            for n in range(ceil(7 * k / 4), ceil(11 * k / 6)):
                r = n - k - T
                if r < 0:
                    continue
                w = (12 * n - 21 * k) // 7
                tot += 1
                a = analyse(n, k, r)["win"] if r >= 1 else True
                b = best_interval(n, k, r)
                bwin = b is not None and b[0] <= w
                okA += a; okB += bwin
                if not (a or bwin):
                    fails.append((n, k, r, w))
    print(f"Erdos-range cases {tot}: two-step wins {okA}, Lemma-5c pencil <= w wins {okB}; neither: {len(fails)}")
    print("cases where neither route wins (n,k,r,w), first 15:", fails[:15])
    if fails:
        print("largest k among failures:", max(f[1] for f in fails))


if __name__ == "__main__" and sys.argv[1] == "routes":
    scan_routes(int(sys.argv[2]), int(sys.argv[3]))
