"""Randomized sanity checks for the hand lemmas in notes/NEW_PATHS.md.
Lemma B (sparse trace): good triple E,F,G, W = union, K any edge, c = |K & W|.
  Requests D_i = (K&W) | P_i, P_1..P_3 a partition of W-K. Any responses R_i (k-sets avoiding D_i,
  free to use new points) give 7 edges with no 2-point transversal.
Lemma 3+3: good triple A1..A3 with union W, B1,B2,B3 with pairwise intersections disjoint from W
  => the six edges have no 2-point transversal.
"""
import random, itertools
def has2cover(edges):
    pts = sorted(set().union(*edges))
    for p in pts:
        rest = [e for e in edges if p not in e]
        if not rest: return True
        if set.intersection(*rest): return True
    return False
def rand_good_triple(k, rng):
    while True:
        n = rng.randint(k+2, 3*k)
        E,F,G = (set(rng.sample(range(n), k)) for _ in range(3))
        if not (E & F & G): return E,F,G,n
def lemmaB(trials=3000, seed=1):
    rng = random.Random(seed); bad = 0
    for _ in range(trials):
        k = rng.randint(3, 9)
        E,F,G,n = rand_good_triple(k, rng)
        W = E|F|G; N = n + 4*k
        K = set(rng.sample(range(N), k))
        rest = list(W-K); rng.shuffle(rest)
        P = [set(rest[i::3]) for i in range(3)]
        Rs = []
        for i in range(3):
            D = (K & W) | P[i]
            avail = [v for v in range(N+3*k) if v not in D]
            Rs.append(set(rng.sample(avail, k)))
        if has2cover([E,F,G,K]+Rs): bad += 1
    return bad
def lemma33(trials=3000, seed=2):
    rng = random.Random(seed); bad = 0
    for _ in range(trials):
        k = rng.randint(3, 8)
        E,F,G,n = rand_good_triple(k, rng)
        W = E|F|G; N = n + 5*k; Bs = []
        for i in range(3):
            forb = set().union(*[b & W for b in Bs]) if Bs else set()
            avail = [v for v in range(N) if v not in forb]
            Bs.append(set(rng.sample(avail, k)))
        if has2cover([E,F,G]+Bs): bad += 1
    return bad
print("Lemma B failures:", lemmaB()); print("Lemma 3+3 failures:", lemma33())
