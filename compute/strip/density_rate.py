"""CORE §91: the density a T-covering family is guaranteed, after padding to member ratio 3/7, as a rate per point.

|C| >= C(n,T)/C(n-k,T)  =>  |C| / C(n,n-k) >= 1/C(n-T, n-k-T).
Padding: add m = ceil(7(n-k)/3) - n >= 0 isolated points (in no member); members are (n-k)-sets of [n+m] with
n-k = floor(3(n+m)/7).  |C| / C(n+m, n-k) >= 1/[C(n-T, n-k-T) * C(n+m, n-k)/C(n, n-k)].
Frankl-Rodl (Keevash-Long Thm 1.1, alpha = 3/7, eps_FR = 1/14) forbids every l in [(n+m)/14, (n-k) - (n+m)/14]
for families of density > (1-delta)^(n+m).  So it applies once  rate := -ln(density bound)/(n+m) < -ln(1-delta).
Exact integer arithmetic (math.comb, logs of exact integers).  usage: py density_rate.py
"""
from math import comb, log, ceil


def rate(k, T, n):
    m = -(-7 * (n - k) // 3) - n
    assert m >= 0 and (n - k) == (3 * (n + m)) // 7
    lb = log(comb(n - T, n - k - T)) + log(comb(n + m, n - k)) - log(comb(n, n - k))
    l = n - 2 * T
    inrange = (n + m) / 14 <= l <= (n - k) - (n + m) / 14
    return lb / (n + m), m, inrange


print('eps   omega/eps   k       rate (per point)   FR range ok')
for eps in [0.04, 0.02, 0.01, 0.005, 0.002, 0.001]:
    for ratio in [2.0, 3.0, 3.9]:
        for k in [10000, 100000]:
            T = round((0.75 + eps) * k)
            n = round(k + T + ratio * eps * k)
            r, m, ok = rate(k, T, n)
            print(f'{eps:<6}{ratio:<12}{k:<8}{r:<19.5f}{ok}')
