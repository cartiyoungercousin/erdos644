"""7INV, part 2: the member-count majorant nu_H(R) = N_H(R) / E N_H(R_u) and its 2-point linear-forms condition.

Balanced colourings with n = 7c (seven classes of size c): |R_u| = 4c, |R_u cap R_v| = 2c for u != v.
For k-sets B, B' with |B cap B'| = i:
    g(i) = P(B in R_u, B' in R_v) / P(B in R_u)^2.
Then E[nu_H(R_u) nu_H(R_v)] = E_{(B,B') in H^2} g(|B cap B'|) exactly, and sum_i h(i) g(i) = 1 for the complete
family (h = pair-intersection law of two uniform k-sets).  We report, per (n,k): the check sum, log2 g / k at the
forced minimum 2k-n, at the typical k^2/n, and the tilted point i* = argmax h(i) g(i) (the intersection size that
carries the 2-point count), with the large-deviation cost -log2 h(i*)/k of having such pairs.
Usage: py -3.14 majorant.py
"""
from math import lgamma, log, exp, comb


def lc(a, b):
    if b < 0 or b > a:
        return float('-inf')
    return lgamma(a + 1) - lgamma(b + 1) - lgamma(a - b + 1)


def lmult(n, parts):
    if any(p < 0 for p in parts) or sum(parts) != n:
        return float('-inf')
    return lgamma(n + 1) - sum(lgamma(p + 1) for p in parts)


def lse(xs):
    xs = [x for x in xs if x > float('-inf')]
    if not xs:
        return float('-inf')
    m = max(xs)
    return m + log(sum(exp(x - m) for x in xs))


def logg(n, k, i):
    c = n // 7
    tot = lmult(n, [2 * c, 2 * c, 2 * c, c])
    terms = []
    for a in range(k - i + 1):
        for b in range(k - i + 1):
            terms.append(lc(k - i, a) + lc(k - i, b) +
                         lmult(n - 2 * k + i, [2 * c - i - a - b, 2 * c - (k - i - a), 2 * c - (k - i - b), c]))
    lp = lse(terms) - tot
    lp1 = lc(n - k, 4 * c - k) - lc(n, 4 * c)
    return lp - 2 * lp1


def main():
    L2 = log(2)
    print('n k | check sum_i h g | log2 g/k at i=2k-6n/7 (min), at k^2/n | i*/k (k^2/n/k) | log2 g(i*)/k | -log2 h(i*)/k')
    for n, k in [(63, 35), (126, 70), (252, 140), (378, 210), (504, 280), (756, 420), (756, 415)]:
        lh = {i: lc(k, i) + lc(n - k, k - i) - lc(n, k) for i in range(max(0, 2 * k - n), k + 1)}
        step = 1 if k <= 80 else max(1, k // 60)
        grid = sorted(set(list(range(min(lh), k + 1, step)) + [2 * k - 6 * n // 7, round(k * k / n)]))
        lg = {i: logg(n, k, i) for i in grid}
        chk = exp(lse([lh[i] + lg[i] for i in lh])) if step == 1 else float('nan')
        lh = {i: lh[i] for i in grid}
        it = round(k * k / n)
        istar = max(lh, key=lambda i: lh[i] + lg[i])
        print('%d %d | %.6f | %+.4f  %+.4f | %.3f (%.3f) | %+.4f | %.4f' % (
            n, k, chk, lg[2 * k - 6 * n // 7] / k / L2, lg[it] / k / L2, istar / k, it / k, lg[istar] / k / L2,
            -lh[istar] / k / L2), flush=True)


def frac7():
    """log2 (fraction of 7-tuples of k-sets compatible with SOME balanced colouring) / k  <=  N log2 7 + 7 log2(C(4n/7,k)/C(n,k)) / k."""
    print('7-point thin set: N, upper bound on log2(fraction of 7-tuples that can be Fano-type sevens)/k (k = 7000)')
    k = 7000
    for N in (1.76, 1.78, 1.80, 1.82, 1.833):
        n = round(N * k)
        m = (4 * n) // 7
        print('  %.3f  %+.3f' % (N, (n * log(7) + 7 * (lc(m, k) - lc(n, k))) / k / log(2)))


if __name__ == '__main__':
    frac7()
    main()
