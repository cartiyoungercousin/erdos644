r"""Complete family K(n,k) as adversary vs Prop 16.A: tau = n-k+1; (7,2) iff NO 7 blocks of size m=n-k cover all pairs of the n points.
If not coverable and n>=T+k then K(n,k) is a (7,2)-family with tau>T, so no strategy wins.  DFS on first uncovered pair.
"""
import itertools, sys
from math import comb

def cover7(n, m, B=7):
    allp = [(x, y) for x in range(n) for y in range(x + 1, n)]
    pm = {p: i for i, p in enumerate(allp)}
    full = (1 << len(allp)) - 1
    blockmask = {}
    def bm(bl):
        v = 0
        for a, b in itertools.combinations(sorted(bl), 2): v |= 1 << pm[(a, b)]
        return v
    def dfs(cov, left):
        if cov == full: return True
        if left == 0: return False
        if bin(full & ~cov).count('1') > left * comb(m, 2): return False
        # first uncovered pair
        un = full & ~cov; i = (un & -un).bit_length() - 1
        x, y = allp[i]
        rest = [z for z in range(n) if z != x and z != y]
        for ex in itertools.combinations(rest, m - 2):
            key = (x, y) + ex
            if key not in blockmask: blockmask[key] = bm(key)
            if dfs(cov | blockmask[key], left - 1): return True
        return False
    return dfs(0, B)

if __name__ == '__main__':
    for k in range(4, 9):
        for T in range((3 * k + 3) // 4, k):
            res = []
            for n in range(T + k, int(3 * T - k / 2) + 1):
                m = n - k
                if m < 2: continue
                if comb(n, m) > 0 and not cover7(n, m):
                    res.append((n, 3 * T - k / 2 - n))
            print('k=%d T=%d n in [%d,%d]: K(n,k) is a (7,2)-family with tau>T at (n, slack 3T-k/2-n)=' % (k, T, T + k, int(3 * T - k / 2)), res); sys.stdout.flush()
