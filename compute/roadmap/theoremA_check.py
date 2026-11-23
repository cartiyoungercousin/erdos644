"""Sanity check of 'Theorem A' (one-anchor Fano template) on random small instances.

Claim: H k-uniform on vertex set V (|V| = n), tau(H) > T, and T >= max_j |B_j| + max pair-sum of
the parts of A_1, where V \ A_1 = B_1 u B_2 u B_3 and A_1 = a_1 u a_2 u a_3 u a_4.  Then the 6
requests D = B_j u a_p u a_q (p,q a pair of the j-th perfect matching of {1,2,3,4}) together with
A_1 give 7 edges with no 2-point transversal, WHATEVER the responses are.
We test the purely set-theoretic core: for random responses R_i (any k-subset of V \ D_i), the
7 sets A_1, R_1..R_6 have no 2-point cover.  (Exhaustive over responses is impossible; random +
adversarial greedy responses are used.)"""
import itertools, random

MATCH = [((0,1),(2,3)), ((0,2),(1,3)), ((0,3),(1,2))]

def has_2cover(sets, n):
    for u in range(n):
        for v in range(u, n):
            if all(u in S or v in S for S in sets): return True
    return False

def trial(n, k, rng):
    V = list(range(n)); rng.shuffle(V)
    A1 = V[:k]; rest = V[k:]
    a = [A1[i::4] for i in range(4)]
    B = [rest[i::3] for i in range(3)]
    sets = [set(A1)]
    for j in range(3):
        for (p, q) in MATCH[j]:
            D = set(B[j]) | set(a[p]) | set(a[q])
            free = [v for v in range(n) if v not in D]
            if len(free) < k: return None           # request too large for this (n,k): skip
            sets.append(set(rng.sample(free, k)))
    return has_2cover(sets, n)

if __name__ == "__main__":
    rng = random.Random(1); bad = 0; tot = 0
    for (n, k) in [(8,4),(9,4),(15,8),(16,8),(22,12),(23,12),(25,12),(29,16),(30,16)]:
        for _ in range(300):
            r = trial(n, k, rng)
            if r is None: continue
            tot += 1; bad += r
    print("trials:", tot, " tuples WITH a 2-cover (should be 0):", bad)
