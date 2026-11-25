"""PEN(1/2) via the centred dumping lemma (Lemma 5c).  Exact integer bookkeeping + tests.

Lemma 5c.  H k-uniform on n points, every (k+r)-set contains a member.  I = [lo, hi] with hi-lo = w,
2w+2 > r.  If members x1, x2 have |x1&x2| = j with hi <= k-j and k+r-2hi <= n-2k+j, then some member y
has |y & x1| in I or |y & x2| in I.  (A = hi pts of x1-x2, hi pts of x2-x1, k+r-2hi outside.)
Pair -> pencil: members x, y with |x&y| = j' give a pencil of weight <= r + |2j'-(k-r)|
(needs n >= k+r+j' in the case 2k-2j' <= k+r).

Usage:  py -3.14 pen_check.py table          (bound vs Lemma 8' 2r+1, slope comparison)
        py -3.14 pen_check.py lemma5 trials  (explicit-set brute force of Lemma 5c)
        py -3.14 pen_check.py sat n k r P    (is there a covering family with no pencil of weight <= P?)
"""
import sys, random, itertools
from math import comb


def best_interval(n, k, r):
    """Return (P, lo, hi, j-window) or None: the pencil bound r + D given by Lemma 5c."""
    w = (r - 1 + 1) // 2 if r >= 1 else 0          # smallest w with 2w+2 > r  (= ceil((r-1)/2))
    while 2 * w + 2 <= r:
        w += 1
    best = None
    for lo in range(0, k + 1):
        hi = lo + w
        if hi > k or k + r - 2 * hi < 0:
            continue
        D = max(abs(2 * j - (k - r)) for j in range(lo, hi + 1))
        # pencil extension needs n >= k+r+j' when 2k-2j' <= k+r
        if any(2 * k - 2 * j <= k + r and n < k + r + j for j in range(lo, hi + 1)):
            continue
        # existence of the pair x1,x2: need j in [jmin, jmax]; covering gives a pair in [l-r, l]
        jmax = k - hi
        jmin = max(0, 3 * k + r - 2 * hi - n)
        l = jmax
        ok = (l - r >= jmin) and (l <= k - 1) and (k + r - l <= n - k)
        if not ok:
            continue
        if best is None or D < best[0] - r:
            best = (r + D, lo, hi, (l - r, l))
    return best


def table():
    print(" k    n     T   r   new pencil bound  Lemma8' 2r+1   tau-bound new  tau-bound C1")
    for k, n, T in [(100, 180, 78), (200, 360, 155), (1000, 1800, 770), (1000, 1830, 780), (1000, 1760, 752)]:
        r = n - k - T
        b = best_interval(n, k, r)
        # (7,2) + P1: 4T-3k-5 <= P  ==> largest T allowed
        def maxT(fn):
            best = None
            for TT in range(k // 2 + 1, n - k + 1):
                rr = n - k - TT
                if rr < 0:
                    break
                P = fn(n, k, rr)
                if P is None:
                    continue
                if 4 * TT - 3 * k - 5 <= P:
                    best = TT
            return best
        tn = maxT(lambda a, b_, c: (best_interval(a, b_, c) or [None])[0])
        to = maxT(lambda a, b_, c: 2 * c + 1)
        print(f"{k:4d} {n:5d} {T:4d} {r:3d}   {b[0] if b else None:8}        {2*r+1:6d}        "
              f"{tn+1 if tn else None:6}        {to+1 if to else None:6}   (3n+3k)/11={(3*n+3*k)/11:.1f} (2n+k)/6+2={(2*n+k)/6+2:.1f}")


def lemma5(trials, seed=1):
    rng = random.Random(seed)
    checked = 0
    for _ in range(trials):
        k = rng.randint(6, 14); r = rng.randint(1, 5); n = rng.randint(k + r + k // 2, 2 * k + 2 * r)
        w = 0
        while 2 * w + 2 <= r:
            w += 1
        lo = rng.randint(0, k); hi = lo + w
        j = rng.randint(0, k)
        if hi > k - j or k + r - 2 * hi < 0 or k + r - 2 * hi > n - 2 * k + j or n < 2 * k - j:
            continue
        V = list(range(n)); rng.shuffle(V)
        common = V[:j]; o1 = V[j:k]; o2 = V[k:2 * k - j]; out = V[2 * k - j:]
        x1 = set(common + o1); x2 = set(common + o2)
        A = o1[:hi] + o2[:hi] + out[:k + r - 2 * hi]
        assert len(A) == k + r
        for drop in itertools.combinations(A, r):
            y = set(A) - set(drop)
            a, b = len(y & x1), len(y & x2)
            assert lo <= a <= hi or lo <= b <= hi, (n, k, r, lo, hi, j)
        checked += 1
    print(f"Lemma 5c brute force: {checked} random instances, every y inside A checked: OK")


def sat(n, k, r, P):
    from pysat.solvers import Cadical153
    sets = [frozenset(c) for c in itertools.combinations(range(n), k)]
    idx = {s: i + 1 for i, s in enumerate(sets)}
    masks = [sum(1 << e for e in s) for s in sets]
    solver = Cadical153()
    for A in itertools.combinations(range(n), k + r):
        solver.add_clause([idx[frozenset(c)] for c in itertools.combinations(A, k)])
    # pencil triples with weight <= P: x3 misses x1&x2, |x3 & y| = t >= (s+k-P)/2
    full = (1 << n) - 1
    ncl = 0
    M = len(sets)
    for a in range(M):
        for b in range(a + 1, M):
            ma, mb = masks[a], masks[b]
            y = ma ^ mb; s = bin(y).count("1")
            if s + k - 2 * min(s, k) > P:      # even the best x3 is too heavy
                continue
            cap = ma & mb
            ys = [e for e in range(n) if y >> e & 1]
            outs = [e for e in range(n) if not ((ma | mb) >> e & 1)]
            for t in range(min(s, k), -1, -1):
                if s + k - 2 * t > P:
                    break
                if k - t > len(outs):
                    continue
                for c1 in itertools.combinations(ys, t):
                    for c2 in itertools.combinations(outs, k - t):
                        x3 = frozenset(c1 + c2)
                        c = idx[x3]
                        if c - 1 in (a, b):
                            continue
                        solver.add_clause([-(a + 1), -(b + 1), -c]); ncl += 1
    res = solver.solve()
    print(f"n={n} k={k} r={r} P={P}: covering family with NO pencil of weight <= P: "
          f"{'EXISTS (SAT)' if res else 'NONE (UNSAT)'}  [{M} sets, {ncl} pencil clauses]")
    return res


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "table":
        table()
    elif cmd == "lemma5":
        lemma5(int(sys.argv[2]))
    elif cmd == "sat":
        sat(*map(int, sys.argv[2:6]))
    elif cmd == "bound":
        print(best_interval(*map(int, sys.argv[2:5])))


def corollary(kmax):
    """Check: for every k <= kmax, n in [k+1, 2k], every T with T+1 > (3n+3k+24)/11 and r = n-k-T >= 0
    has the Lemma-5c size conditions AND 4T-3k-6 >= pencil bound (so P1 gives a seven).
    Reports the (n,k,T) that escape, i.e. where the corollary tau <= (3n+3k+24)/11 is NOT certified."""
    esc = []
    for k in range(4, kmax + 1):
        for n in range(k + 1, 2 * k + 1):
            for T in range(0, n - k + 1):
                if 11 * (T + 1) <= 3 * n + 3 * k + 24:
                    continue
                r = n - k - T
                b = best_interval(n, k, r)
                if b is None or 4 * T - 3 * k - 6 < b[0]:
                    esc.append((n, k, T, r, b))
    print(f"corollary tau <= (3n+3k+24)/11 for n <= 2k, k <= {kmax}: {len(esc)} uncertified (n,k,T)")
    if esc:
        print("  largest k uncertified:", max(e[1] for e in esc), " examples:", esc[:8])


if __name__ == "__main__" and sys.argv[1] == "corollary":
    corollary(int(sys.argv[2]))
