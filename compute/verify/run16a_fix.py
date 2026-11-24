import random, sys
from math import comb
from twin13_16a import prop16A
rnd = random.Random(5)
for c in (1, 2, 3):
    tot = 0; bad = []
    for k in range(5, 11):
        for T in range((3*k+3)//4, k):
            for n in range(T + k, int(3*T - k/2 - c) + 1):
                if comb(n - T, k) ** 2 > 6000: continue
                if n - 2*T + c > n - k: continue
                r = prop16A(k, T, n, rnd, c=c)
                tot += 1
                if r[2]: bad.append(((k,T,n), r[1], r[3][:1]))
    print('kernel shift c=%d (instances with n<=3T-k/2-c): %d tested, failing: %s' % (c, tot, bad)); sys.stdout.flush()
