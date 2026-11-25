"""Non-degenerate tests at T=2: sample random k-uniform-ish families with tau>=3, edge-minimalise to a
tau-critical family (every proper subfamily has tau<=2, hence (7,2) iff it has >=8 members, else it is
not a counterexample), then locally minimalise (member removal / point deletion) and run all checks.
Usage: py -3.14 minframe_crit.py k n trials seed"""
import sys, random, itertools
from minframe import tau, is72, Vof, is_ce, local_min, check, reduce_local


def sample(k, n, rnd, mmax):
    allsets = [frozenset(c) for c in itertools.combinations(range(n), k)]
    rnd.shuffle(allsets)
    m = rnd.randint(8, mmax)
    return allsets[:m]


def edge_min(H, rnd):
    H = list(H)
    order = list(range(len(H)))
    rnd.shuffle(order)
    keep = list(H)
    for idx in order:
        B = H[idx]
        G = [x for x in keep if x != B]
        if G and tau(G, Vof(G)) >= 3:
            keep = G
    return keep


if __name__ == "__main__":
    k, n, trials, seed = map(int, sys.argv[1:5])
    T = 2
    rnd = random.Random(seed)
    seen = set()
    nfail = 0
    nce = 0
    for _ in range(trials):
        H = sample(k, n, rnd, min(30, 3 * n))
        if tau(H, Vof(H)) < 3:
            continue
        H = edge_min(H, rnd)
        if len(H) < 8 or not is_ce(H, T):
            continue
        H = reduce_local(H, T, rnd)
        assert local_min(H, T) and is_ce(H, T)
        c = tuple(sorted(tuple(sorted(B)) for B in H))
        if c in seen:
            continue
        seen.add(c)
        nce += 1
        f = check(H, T)
        if f:
            nfail += 1
            print("FAIL", c, f[:4])
    sizes = sorted(sum(len(b) for b in c) for c in seen)
    print(f"k={k} n={n} T=2: distinct locally-minimal counterexamples checked={nce} failures={nfail} "
          f"members range={sorted(set(len(c) for c in seen))} ||H|| range={sizes[:1]}..{sizes[-1:]}")
