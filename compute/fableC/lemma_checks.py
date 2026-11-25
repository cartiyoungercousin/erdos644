r"""FABLE_C: brute-force checks of Lemmas 2.2, 2.3 and 5.2 and of Theorem 2.5 on random small set systems.
[computed exact; the statements are proved by hand in notes/FABLE_C.md]"""
import random, itertools
from classify_sevens import U_of
rng = random.Random(7); pc = lambda m: bin(m).count('1')
def covers_all(sets, n): return U_of(sets, n) == 0
n23 = n22 = n52 = n25 = 0
for trial in range(20000):
    n = rng.randint(4, 9); m = rng.randint(1, 6); FULL = (1 << n) - 1
    A = [rng.randrange(1, FULL + 1) for _ in range(m)]; B = rng.randrange(0, FULL + 1)
    U = U_of(A, n)
    assert covers_all(A + [B], n) == (U & ~B == 0); n23 += 1                       # Lemma 2.3
    A2 = [a | rng.randrange(0, FULL + 1) for a in A]
    assert U_of(A2, n) & ~U == 0; n22 += 1                                          # Lemma 2.2
    F = FULL & ~U; S = rng.randrange(0, FULL + 1); D = F & rng.randrange(0, FULL + 1)
    assert U_of(A + [S | D], n) == U_of(A + [S], n); n52 += 1                       # Lemma 5.2
# Theorem 2.5: random hypergraphs with (p,2) for p = m+1: W(any m edges) is a transversal
def covers(P, E): return all(P & e for e in E)
for trial in range(3000):
    n = rng.randint(4, 7); FULL = (1 << n) - 1; ne = rng.randint(3, 6); m = 2
    H = [rng.randrange(1, FULL + 1) for _ in range(ne)]
    P2 = [1 << x | 1 << y for x in range(n) for y in range(x, n)]
    if not all(any(covers(P, T) for P in P2) for T in itertools.combinations(H, min(m + 1, ne))): continue
    for T in itertools.combinations(H, m):
        W = 0
        for P in P2:
            if covers(P, T): W |= P
        assert all(W & e for e in H); n25 += 1
print(f"Lemma 2.3: {n23} cases ok; Lemma 2.2: {n22} ok; Lemma 5.2: {n52} ok; Theorem 2.5 with (3,2), two edges: {n25} cases ok")
