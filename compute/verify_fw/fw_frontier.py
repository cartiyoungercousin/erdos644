"""Independent recomputation of c0(nu), the thresholds 1.784 / 1.7994 / eps <= 0.0074, and the k = 2000 table.

Usage:
  py -3.14 fw_frontier.py entropy                # c0(nu) entropy limit, monotonicity, thresholds
  py -3.14 fw_frontier.py exact K1,K2,..         # exact finite-k frontier for nu in {7/4, 1.8, 11/6, 2}
  py -3.14 fw_frontier.py slope K S1,S2,..       # e_max table (P1 + Theorem FW + 3/11 bound)
"""
import sys
from math import comb, log, floor
from fractions import Fraction


def H(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * log(x) - (1 - x) * log(1 - x)


def f(rho, nu):
    # > 0  <=>  condition of Theorem FW holds asymptotically
    return nu * H(1 / nu) - (1 + rho) * H(rho / (1 + rho)) - nu * H((1 + rho) / (2 * nu))


def c0(nu):
    lo, hi = 0.0, 0.4
    assert f(1e-12, nu) > 0 and f(hi, nu) < 0, (nu, f(hi, nu))
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid, nu) > 0:
            lo = mid
        else:
            hi = mid
    return lo


def root(g, a, b):
    ga = g(a)
    for _ in range(200):
        m = (a + b) / 2
        if (g(m) > 0) == (ga > 0):
            a = m
        else:
            b = m
    return (a + b) / 2


def entropy():
    for nu in [1.70, 1.75, 1.78, 1.784, 1.79, 1.7994, 1.8, 11 / 6, 1.9, 2.0]:
        c = c0(nu)
        # check f is decreasing in rho on [0, c] (unique root) on a grid
        mono = all(f(c * i / 400, nu) > f(c * (i + 1) / 400, nu) for i in range(400))
        print(f"nu={nu:.5f}  c0={c:.5f}  f decreasing on [0,c0]: {mono}  (1+c0)/(2nu)={(1+c)/(2*nu):.4f} < 1/2")
    grid = [1.70 + 0.001 * i for i in range(331)]
    vals = [c0(v) for v in grid]
    inc = all(vals[i] < vals[i + 1] for i in range(len(vals) - 1))
    print(f"c0 strictly increasing on [1.70, 2.03] (step .001): {inc}")
    n1 = root(lambda v: c0(v) - (v - 1.75), 1.751, 1.9)
    n2 = root(lambda v: 11 * c0(v) / 8 - (v - 1.75), 1.751, 1.9)
    n3 = root(lambda v: 5 * c0(v) / 4 - (v - 1.75), 1.751, 1.9)
    print(f"c0(nu) = nu - 7/4            at nu = {n1:.5f}   (note: 1.7840; exception impossible below)")
    print(f"11 c0(nu)/8 = nu - 7/4       at nu = {n2:.5f}   (note: 1.7994; beats 3/11 below)")
    print(f"5 c0(nu)/4 = nu - 7/4        at nu = {n3:.5f}   (e <= s/5 + o(k) actually holds up to here)")
    e1 = c0(1.75) / 4
    e2 = root(lambda e: c0(1.75 + 5 * e) - 4 * e, 1e-4, 0.03)
    print(f"eps threshold c0(7/4)/4 = {e1:.5f} (note 0.0074);  sharp 4eps = c0(7/4+5eps): eps = {e2:.5f}")


def primes_upto(m):
    s = bytearray([1]) * (m + 1)
    s[0] = s[1] = 0
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return s


class Ctx:
    def __init__(self, n, k):
        self.n, self.k = n, k
        self.isp = primes_upto(2 * k + 10)
        # prefix sums of C(n,i)
        self.row = [1]
        for i in range(1, k + 2):
            self.row.append(self.row[-1] * (n - i + 1) // i)
        self.pref = [0]
        for v in self.row:
            self.pref.append(self.pref[-1] + v)  # pref[p] = sum_{i<p} C(n,i)
        self.cnk = comb(n, k)

    def least_prime(self, r):
        p = (self.k + r + 2) // 2  # ceil((k+r+1)/2)
        while not self.isp[p]:
            p += 1
        return p

    def holds(self, r, published=False):
        k = self.k
        p = self.least_prime(r)
        if p > k:
            return False, p
        assert 2 * p >= k + 1 and 2 * p >= k + r + 1
        B = self.row[p - 1] if published else self.pref[p]
        return self.cnk > comb(k + r, r) * B, p


def frontier(ctx, published=False):
    r = 0
    first_fail = None
    holds_after = []
    while True:
        ok, p = ctx.holds(r, published)
        if not ok:
            first_fail = r
            break
        r += 1
    # look for non-monotone recoveries just beyond
    for rr in range(first_fail + 1, first_fail + 40):
        ok, _ = ctx.holds(rr, published)
        if ok:
            holds_after.append(rr)
    return first_fail - 1, holds_after


def exact(ks):
    for nu in [Fraction(7, 4), Fraction(9, 5), Fraction(11, 6), Fraction(2)]:
        for k in ks:
            n = floor(nu * k)
            ctx = Ctx(n, k)
            R, rec = frontier(ctx)
            Rp, recp = frontier(ctx, published=True)
            print(f"nu={float(nu):.4f} k={k} n={n}: all r<=R pass, R={R} (R/k={R/k:.4f}); "
                  f"recoveries after first fail: {rec[:5]};  with C(n,p-1): R={Rp} ({Rp/k:.4f}); "
                  f"entropy c0={c0(float(nu)):.4f}", flush=True)


def best_weight(ctx, r):
    """Smallest pencil weight Theorem FW guarantees at this r, over ALL primes (k+1)/2 <= p <= k
    satisfying the count, using branch 2 (2p >= k+r, weight 2p-k) or branch 1 (2p < k+r,
    weight k+2r-2p, needs room p >= 2k+r-n). None if no prime works."""
    n, k = ctx.n, ctx.k
    best = None
    ck = comb(k + r, r)
    for p in range((k + 2) // 2, k + 1):
        if not ctx.isp[p]:
            continue
        if not ctx.cnk > ck * ctx.pref[p]:
            break  # pref increasing in p
        if 2 * p >= k + r:
            w = 2 * p - k
        elif p >= 2 * k + r - n:
            w = k + 2 * r - 2 * p
        else:
            continue
        best = w if best is None else min(best, w)
    return best


def slope_full(k, ss):
    assert k % 4 == 0
    for s in ss:
        n = 7 * k // 4 + s
        ctx = Ctx(n, k)
        b24 = (3 * s + 24) // 11
        emax = None
        route = None
        for e in range(s + 1, -1, -1):
            T = e + 3 * k // 4 - 1
            r = n - k - T
            if e > b24:
                continue
            w = best_weight(ctx, r)
            if w is None or w > 4 * T - 3 * k - 6:
                emax = e
                route = "3/11" if e == b24 else "FW"
                break
        print(f"[full] k={k} s={s}: e_max={emax} route={route}  (3s+24)/11 floor={b24}  "
              f"(s+11)/5={(s+11)/5:.1f}", flush=True)


def slope(k, ss):
    assert k % 4 == 0
    for s in ss:
        n = 7 * k // 4 + s
        ctx = Ctx(n, k)
        emax = None
        b24 = (3 * s + 24) // 11
        b21 = (3 * s + 21) // 11
        for e in range(s + 1, -1, -1):  # r = s+1-e >= 0
            T = e + 3 * k // 4 - 1
            r = n - k - T
            assert r == s + 1 - e
            if e > b24:
                continue
            ok, p = ctx.holds(r)
            fires = ok and (2 * p - k <= 4 * T - 3 * k - 6)
            if not fires:
                emax = e
                break
        # also the hand formula
        print(f"k={k} s={s}: e_max={emax}  (3s+24)/11 floor={b24}  (3s+21)/11 floor={b21}  "
              f"s/5+2={s/5+2:.1f}", flush=True)


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "entropy":
        entropy()
    elif cmd == "exact":
        exact([int(x) for x in sys.argv[2].split(",")])
    elif cmd == "slope":
        slope(int(sys.argv[2]), [int(x) for x in sys.argv[3].split(",")])
    elif cmd == "slack":
        # largest r (all r' <= r) with an FW pencil (any prime, both branches) of weight <= r + S
        k = int(sys.argv[2])
        for nu in [Fraction(7, 4), Fraction(11, 6)]:
            n = floor(nu * k)
            ctx = Ctx(n, k)
            for S in ["2sqrtk", "2g+1", "0"]:
                ps = [q for q in range(2, k + 1) if ctx.isp[q]]
                g = max(b - a for a, b in zip(ps, ps[1:]))
                slack = {"2sqrtk": 2 * k ** 0.5, "2g+1": 2 * g + 1, "0": 0}[S]
                r = 0
                while True:
                    w = best_weight(ctx, r)
                    if w is None or w > r + slack:
                        break
                    r += 1
                print(f"k={k} n={n} nu={float(nu):.4f} slack {S} (={slack:.1f}, g={g}): "
                      f"R={r-1} ({(r-1)/k:.4f})", flush=True)
    elif cmd == "slopefull":
        slope_full(int(sys.argv[2]), [int(x) for x in sys.argv[3].split(",")])
