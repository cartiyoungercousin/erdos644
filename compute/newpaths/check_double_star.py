"""Randomized check of the s+3 lemma (NEW_PATHS §6.1): P_1..P_s (s = 3 or 4) with empty common
intersection, U their union; C_1,C_2,C_3 edges with C_i∩C_j∩U = ∅ (i != j)  =>  no 2-point cover.
Also the negative control: with only TWO such centres a 2-cover can exist."""
import random
from check_lemmas import has2cover
def trial(k, s, rng, ncent=3):
    while True:
        n = rng.randint(k + 2, 2 * k + 2)
        P = [set(rng.sample(range(n), k)) for _ in range(s)]
        if not set.intersection(*P): break
    U = set().union(*P); N = n + 4 * k; C = []
    for _ in range(ncent):
        forb = set().union(*[c & U for c in C]) if C else set()
        avail = [v for v in range(N) if v not in forb]
        C.append(set(rng.sample(avail, k)))
    return has2cover(P + C)
rng = random.Random(7)
for s in (3, 4):
    print(f"s={s}: failures with 3 centres:", sum(trial(rng.randint(3, 8), s, rng) for _ in range(4000)),
          "| 2-covers found with only 2 centres:", sum(trial(rng.randint(3, 8), s, rng, 2) for _ in range(4000)))
