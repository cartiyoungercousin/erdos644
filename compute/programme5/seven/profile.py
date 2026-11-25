"""Programme 5 (seven): exact log-binomial profile of the member-free down-set for the CTS test families.

Window: n = floor((7/4+d)k), T = ceil((3/4+e)k), r = n-k-T, m4 = floor(4n/7) (balanced |R_u|).
Family R (binomial random, density p = 2 ln C(n,k+r) / C(k+r,r)); the same p is the INV-P coset-union density.
Columns (bits = log2):
  ub      : 4n/7 >= k+r ? (the union bound alone certifies a seven iff this holds; slope 3/7)
  phi4    : log2 of the whp upper bound 2 p C(m4,k) on phi(m4) = P(random m4-set contains a member)
  jump    : k+r - m0, m0 = least m with 2 p C(m,k) >= 1/2 (width of the late sharp threshold, levels)
  thin    : lower bound (1-f) n/(n-m*) on tau*_b, m* = largest m with f = 2 p C(m,k) <= 2^-10 (thin iff > 7/3)
  block   : (d-3e)k - 2 log2(4n) - 3 > 0  =>  whp no (W,d)-complete block with |W| >= (7/4-e)k+2d+3
  layer   : log2 of the least size C(n,k)/C(k+r,r) of a covering layer, against log2(n^2+n+1)+1 (layer excluded if larger)
  jans    : log2( C(k+r,r) / C(m4,k) ): how many bits above the covering minimum the density must be for the
            Janson/union-bound branch (E_u >= ln 7 at |R_u| = m4) to apply
Usage: py -3.14 profile.py [k ...]
"""
import sys
from math import lgamma, log, log2, floor, ceil


def lc(a, b):
    if b < 0 or b > a:
        return float('-inf')
    return (lgamma(a + 1) - lgamma(b + 1) - lgamma(a - b + 1)) / log(2)


def row(k, d, e):
    n = floor((7 / 4 + d) * k)
    T = ceil((3 / 4 + e) * k)
    r = n - k - T
    if r < 1:
        return None
    m4 = (4 * n) // 7
    lNb = lc(k + r, r)
    lp = log2(2 * lc(n, k + r) * log(2)) - lNb
    phi4 = 1 + lp + lc(m4, k)
    m0 = next(m for m in range(k, k + r + 1) if 1 + lp + lc(m, k) >= -1)
    mstar = max(m for m in range(k, k + r + 1) if 1 + lp + lc(m, k) <= -10)
    thin = (1 - 2 ** (1 + lp + lc(mstar, k))) * n / (n - mstar)
    block = (d - 3 * e) * k - 2 * log2(4 * n) - 3
    layer = lc(n, k) - lNb
    jans = lNb - lc(m4, k)
    return n, T, r, m4, m4 >= k + r, phi4, k + r - m0, thin, block, layer, log2(n * n + n + 1) + 1, jans


def main():
    ks = [int(a) for a in sys.argv[1:]] or [2000, 10000, 100000]
    print(__doc__.split('Usage')[0])
    print('%7s %5s %6s | %7s %6s %4s %5s %3s | %10s %5s %6s %6s %9s %8s' % (
        'k', 'd', 'e/d', 'n', 'T', 'r', 'm4', 'ub', 'phi4', 'jump', 'thin', 'block', 'layer', 'jans'))
    for k in ks:
        for d in (0.01, 0.04, 0.08):
            for f in (0.0, 0.1, 0.18, 0.25, 0.3):
                x = row(k, d, f * d)
                if x is None:
                    continue
                n, T, r, m4, ub, phi4, jump, thin, block, layer, lay0, jans = x
                print('%7d %5.2f %6.2f | %7d %6d %4d %5d %3s | %10.0f %5d %6.3f %6.0f %9.0f %8.0f' % (
                    k, d, f, n, T, r, m4, 'Y' if ub else 'n', phi4, jump, thin, block, layer, jans))


if __name__ == '__main__':
    main()
