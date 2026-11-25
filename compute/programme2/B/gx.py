r"""G(x) = E_{T ~ Bin(V'', x)} 8^{rk V'' - rk(V'' - T)}  (= sum over lambda in D (x) F2^3 of x^{wt lambda}, Moebius,
notes 5.7), estimated by sampling at x = 7^{-1/2}, for random columns and for planted short dual words.
[computed, Monte Carlo; the identity itself is proved by hand]"""
import random, sys, os, math
sys.path.insert(0, os.path.dirname(__file__))
from b1 import rank
def G(cols, x, samples, rng):
    rk = rank(cols); acc = 0.0
    for _ in range(samples):
        rest = [c for c in cols if rng.random() >= x]
        acc += 8.0 ** (rk - rank(rest))
    return acc / samples
rng = random.Random(1); N = 300; M = 15; x = 7 ** -0.5
for kind, q in [('rand', 0), ('series', 5), ('series', 20), ('triads', 20), ('coloops', 3)]:
    cols = [rng.getrandbits(M) | (1 << 40) for _ in range(N)]
    for t in range(q):
        sz = {'series': 2, 'triads': 3, 'coloops': 1}.get(kind, 0)
        for y in rng.sample(range(N), sz): cols[y] |= 1 << (M + t)
    g = G(cols, x, 400, rng)
    pred = {'series': (1 + 7 * x**2) ** q, 'triads': (1 + 7 * x**3) ** q, 'coloops': (1 + 7 * x) ** q}.get(kind, 1.0)
    print(dict(kind=kind, q=q, N=N, G=round(g, 3), isolated_word_prediction=round(pred, 3)))
