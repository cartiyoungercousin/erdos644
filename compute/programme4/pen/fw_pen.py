"""Programme 4, PEN via Frankl-Wilson counting (see notes/PROGRAMME4_PEN.md, Theorem FW and Corollary).

Lemma FW (proved in the note): p prime, (k+1)/2 <= p <= k, F a family of k-subsets of [n] with no two members
meeting in exactly k-p points  =>  |F| <= sum_{i<p} C(n,i).
Covering: a (k+r)-covering k-uniform family has |H| >= C(n,k)/C(k+r,r).
So if C(n,k) > C(k+r,r) * sum_{i<p} C(n,i), H has x1,x2 with |x1 ^ x2| = 2p, hence a pencil of weight
<= r + |2p-(k+r)| (needs p >= 2k+r-n when 2p < k+r).

Modes (py -3.14 fw_pen.py MODE ...):
  check K        exact integer checks of the lemma's residue step, all k <= K
  frontier       largest r/k with a usable prime, exact at several k, n/k in {1.75,...,2}; entropy limit too
  limits         entropy limits: FW with band (eta=1/2), FW ceiling (p ~ k/2), star witness for density-only
  slope K...     for each k: n in [ceil(7k/4), floor(11k/6)], largest tau not excluded by
                 P1 + (FW pencil or the 3/11 bound); prints e_max(s) and the FW-only region
"""
import sys
from math import comb, log, ceil, floor


def primes_upto(m):
    s = bytearray([1]) * (m + 1); s[0:2] = b"\x00\x00"
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(m + 1) if s[i]]


def check(K):
    # for (k+1)/2 <= p <= k: the i in [0,k-1] with i = k (mod p) are exactly {k-p}
    bad = 0
    for k in range(2, K + 1):
        for p in primes_upto(k):
            if 2 * p < k + 1:
                continue
            hits = [i for i in range(k) if (i - k) % p == 0]
            bad += hits != [k - p]
    print(f"check: residue step for all k <= {K}: {bad} exceptions")


class Table:
    """cumulative binomial sums for fixed n"""
    def __init__(self, n):
        self.n = n; self.cum = []; c = 1; t = 0
        for i in range(n + 1):
            t += c; self.cum.append(t); c = c * (n - i) // (i + 1)

    def below(self, p):  # sum_{i<p} C(n,i)
        return self.cum[p - 1] if p >= 1 else 0


def fw_weight(n, k, r, tab, P):
    """least pencil weight r+|2p-k-r| over usable primes p, or None"""
    lhs = comb(n, k); cr = comb(k + r, r); best = None
    for p in P:
        if 2 * p < k + 1 or p > k:
            continue
        if 2 * p < k + r and p < 2 * k + r - n:
            continue
        if lhs > cr * tab.below(p):
            w = r + abs(2 * p - k - r)
            best = w if best is None else min(best, w)
    return best


def H(x):
    return 0.0 if x <= 0 or x >= 1 else -x * log(x) - (1 - x) * log(1 - x)


def frontier():
    print("Entropy limit (k -> oo), eta=0: largest rho=r/k with (1+rho)H(rho/(1+rho)) + nu H((1+rho)/(2nu)) < nu H(1/nu)")
    for nu in (1.75, 1.7857, 1.8, 1.8333, 1.9, 2.0):
        lo, hi = 0.0, 0.5
        for _ in range(60):
            m = (lo + hi) / 2
            ok = (1 + m) * H(m / (1 + m)) + nu * H((1 + m) / (2 * nu)) < nu * H(1 / nu)
            lo, hi = (m, hi) if ok else (lo, m)
        print(f"  nu={nu:.4f}: rho_max = {lo:.4f}")
    print("Exact: largest r with an FW pencil of weight <= r + 2*sqrt(k) (prime-gap slack), and with any weight")
    for k in (200, 500, 1000, 2000):
        P = primes_upto(k)
        for nu in (1.75, 1.8333, 2.0):
            n = ceil(nu * k) if nu < 2 else 2 * k - 1
            tab = Table(n); r_near = r_any = None
            for r in range(0, k // 4):
                w = fw_weight(n, k, r, tab, P)
                if w is None:
                    break
                r_any = r
                if w <= r + 2 * k ** 0.5:
                    r_near = r
            print(f"  k={k:5d} n={n:5d} (n/k={n/k:.3f}): r_max(weight<=r+2sqrt k)={r_near} ({(r_near or 0)/k:.4f}k), "
                  f"r_max(any)={r_any} ({(r_any or 0)/k:.4f}k)", flush=True)


def bisect(f):
    lo, hi = 0.0, 0.5
    for _ in range(60):
        m = (lo + hi) / 2
        lo, hi = (m, hi) if f(m) else (lo, m)
    return lo


def limits():
    print("rho = r/k limits as k -> oo.  cov(rho) = (1+rho)H(rho/(1+rho)) = -log density lower bound of covering /k")
    cov = lambda m: (1 + m) * H(m / (1 + m))
    for nu in (1.75, 1.8, 1.8333, 1.9, 2.0):
        full = nu * H(1 / nu)
        fw = lambda eta: bisect(lambda m: cov(m) + nu * H((1 + (1 - eta) * m) / (2 * nu)) < full)
        ceil_ = bisect(lambda m: cov(m) + nu * H(1 / (2 * nu)) < full)
        # star {B : B contains S}, |S| = k/2: all distances < k; -log density / k:
        star = full - (nu - 0.5) * H(0.5 / (nu - 0.5))
        st = bisect(lambda m: cov(m) < star)
        print(f"  nu={nu:.4f}: FW eta=0 {fw(0):.4f}, FW eta=1/2 {fw(0.5):.4f}, FW ceiling (2p=k) {ceil_:.4f}, "
              f"density-only impossible beyond {st:.4f}")
    c0 = lambda nu: bisect(lambda m: cov(m) + nu * H((1 + m) / (2 * nu)) < nu * H(1 / nu))
    def root(g, a, b):
        for _ in range(60):
            m = (a + b) / 2
            a, b = (m, b) if g(m) > 0 else (a, m)
        return a
    nu1 = root(lambda nu: c0(nu) - (nu - 1.75), 1.75, 1.9)
    nu2 = root(lambda nu: 11 * c0(nu) / 8 - (nu - 1.75), 1.75, 1.9)
    print(f"  r <= s+1 always inside FW range (c0(nu) >= nu-7/4) for nu <= {nu1:.4f};"
          f" FW+P1 beats 3/11 (s < 11 c0(nu)/8) for nu < {nu2:.4f}")


def slope(ks):
    for k in ks:
        P = primes_upto(k)
        print(f"k={k}: s, e_max(P1+FW or 3/11), e_3/11, route   [e = tau - 3k/4, s = n - 7k/4]")
        for n in range(ceil(7 * k / 4), floor(11 * k / 6) + 1, max(1, k // 200)):
            tab = Table(n)
            t311 = floor((3 * n + 3 * k + 24) / 11)
            tau = t311; route = "3/11"
            # largest tau <= t311 not excluded by FW + P1; scan downwards
            while tau > 0:
                T = tau - 1; r = n - k - T
                w = fw_weight(n, k, r, tab, P) if 0 <= r < k // 4 else None
                if w is not None and w <= 4 * T - 3 * k - 6:
                    tau -= 1; route = "FW"; continue
                break
            s = n - 7 * k / 4
            print(f"  s={s:8.2f} e_max={tau - 3*k/4:8.2f} e_3/11={t311 - 3*k/4:8.2f} (s/5={s/5:7.2f}) route={route}",
                  flush=True)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "check":
        check(int(sys.argv[2]))
    elif mode == "frontier":
        frontier()
    elif mode == "limits":
        limits()
    elif mode == "slope":
        slope([int(a) for a in sys.argv[2:]])
