import random, sys
from twin13_16a import prop16A
rnd = random.Random(11)
for k in range(5, 10):
    for T in range((3*k+3)//4, k):
        for n in range(T + k, int(3*T - k/2) + 1):
            from math import comb
            if comb(n - T, k) * comb(n - T, k) > 4000: continue
            r = prop16A(k, T, n, rnd)
            print((k, T, n), 'slack', 3*T - k/2 - n, r[0], r[1], 'fails', r[2], r[3][:1]); sys.stdout.flush()
