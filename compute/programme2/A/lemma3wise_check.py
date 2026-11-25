r"""Lemma A0: if every <=3 members of H (sets of size <= k) share a point, then tau(H) <= (k+1)/2.
Exhaustive check over random 3-wise intersecting families (built by rejection) on n <= 10 points."""
import itertools, random, sys
from theorem_a_check import transversals
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
seen = worst = 0
for _ in range(20000):
    n = rng.randint(3, 10); k = rng.randint(1, n)
    H = []
    for _ in range(rng.randint(1, 40)):
        B = sum(1 << v for v in rng.sample(range(n), rng.randint(1, k)))
        if all(B & C & D for C in H + [B] for D in H + [B]): H.append(B)
    tau = min(bin(M).count('1') for M in transversals(n, H))
    seen += 1; worst = max(worst, tau - (k + 1) / 2)
    assert tau <= (k + 1) / 2, (n, k, H)
print({'families': seen, 'max tau-(k+1)/2': worst})
