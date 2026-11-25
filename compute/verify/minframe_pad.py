"""Lemma 1 (padding) random test + negative control for minframe.check."""
import random, itertools
from minframe import tau, is72, Vof, check, has2

rnd = random.Random(7)
tested = 0
for _ in range(4000):
    n = rnd.randint(3, 8)
    k = rnd.randint(1, 4)
    m = rnd.randint(1, 11)
    H = list({frozenset(rnd.sample(range(n), rnd.randint(1, min(k, n)))) for _ in range(m)})
    V = Vof(H)
    if not is72(H, V):
        continue
    # pad to uniform k with fresh points
    fresh = n
    P = []
    for B in H:
        extra = frozenset(range(fresh, fresh + k - len(B)))
        fresh += k - len(B)
        P.append(B | extra)
    Vp = Vof(P)
    assert all(len(B) == k for B in P)
    assert is72(P, Vp), ("padding broke (7,2)", H)
    assert tau(P, Vp) == tau(H, V), ("tau changed", H, tau(P, Vp), tau(H, V))
    tested += 1
print("Lemma 1 padding: tested", tested, "random (7,2)-families, tau(padded)==tau(orig) and (7,2) preserved in all")

# negative control: checks must fail on non-minimal families
H = [frozenset({1}), frozenset({2}), frozenset({1, 3})]
print("neg control (non-antichain, T=1):", check(H, 1)[:4])
H = [frozenset({1, 2}), frozenset({3, 4}), frozenset({5, 6})]  # not even (7,2), but check L3/L4 behaviour
print("neg control (3 disjoint pairs, T=2):", check(H, 2)[:4])
