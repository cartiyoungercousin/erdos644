"""Finite-k check of the S0 codimension hypothesis via counting (exact integers):
for k = 4..400, every r >= 0 and T >= ceil(3k/4) with n = k + r + T < 11k/6:
  dim C0 >= ceil(log2 |H|) >= ceil(log2( C(n,k+r) / C(n-k,r) ))  (|H| C(n-k,r) >= C(n,k+r), double counting)
  e = codim(C0) - 1 <= n - ceil(log2 lower) - 1.   Report the (k, r, T) where this exceeds (k-1)/2 [4|k form],
  and where it exceeds min((k-1)/2, n - 3k/2) or |H| <= 2^(n/2) is not excluded [k = 2 mod 4 form]."""
from math import comb
def clog2_ratio(a, b):           # ceil(log2(a/b)) for positive integers, exact
    t = (a - 1) // b + 1 if a % b else a // b   # ceil(a/b) >= a/b ; use floor-safe: find least j with 2^j * b >= a
    j = max(0, a.bit_length() - b.bit_length() - 1)
    while (b << j) < a: j += 1
    return j
bad4 = []; bad2 = []; tot = 0
for k in range(4, 401, 2):
    for T in range(-(-3 * k // 4), 2 * k):
        for r in range(0, k):
            n = k + r + T
            if 6 * n >= 11 * k: break
            tot += 1
            lo = clog2_ratio(comb(n, k + r), comb(n - k, r))     # |H| >= 2^(lo-1) at least; use lo-1 to be safe
            e_max = n - (lo - 1) - 1
            if k % 4 == 0 and 2 * e_max > k - 1: bad4.append((k, r, T))
            if k % 4 == 2 and (2 * e_max > k - 1 or e_max > n - 3 * k / 2 or 2 * (lo - 1) <= n): bad2.append((k, r, T))
print('triples checked:', tot)
print('4|k: hypothesis not guaranteed by counting at', len(bad4), 'triples; largest k:', max([b[0] for b in bad4], default=None))
print('k=2 mod 4: not guaranteed at', len(bad2), 'triples; largest k:', max([b[0] for b in bad2], default=None))
print('first few 4|k failures:', bad4[:8]); print('largest-k 2mod4 failures:', sorted(bad2)[-5:])
