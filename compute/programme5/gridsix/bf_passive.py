"""Brute-force check [computed exact on sets]: Theorem P's passive answers lose to the grid frame (drop E).
k = 70 (1 unit = k/14 = 5 points), T = 59 (t = 0.843 < 6/7).  Cells: X 30, Y 25, A 35, B 35, Ep 15, Fd 4, Gd 9,
Z = F&G 1 point.  E = X|Y|Ep, F = X|B|Fd|Z, G = Y|A|Gd|Z, K = A|B.  Passive answer to R: (X|Y|A|B) - R plus fresh
outside points (mass k).  Requests (all contain Z): R1 = A|X[:23], R2 = B|Y[:23], R3 = A|B[:14]|X[23:]|Y[23:],
R4 = A|B[14:]|Y[23:].  Claim: {F,G,K,M1..M4} has no 2-point transversal (a good seven without E)."""
import itertools
k, T = 70, 59
pt = iter(range(10 ** 6)); take = lambda c: [next(pt) for _ in range(c)]
X, Y, A, B, Ep, Fd, Gd, Z = take(30), take(25), take(35), take(35), take(15), take(4), take(9), take(1)
E = set(X + Y + Ep); F = set(X + B + Fd + Z); G = set(Y + A + Gd + Z); K = set(A + B)
assert len(E) == len(F) == len(G) == len(K) == k
live = set(X + Y + A + B)
R = [set(A + X[:23] + Z), set(B + Y[:23] + Z), set(A + B[:14] + X[23:] + Y[23:] + Z), set(A + B[14:] + Y[23:] + Z)]
assert all(len(r) <= T for r in R), [len(r) for r in R]
M = []
for r in R:
    m = live - r
    m |= set(take(k - len(m)))
    assert len(m) == k and not (m & r); M.append(m)
n = next(pt)
def good(mem):
    for x in range(n):
        for y in range(x, n):
            if all(x in S or y in S for S in mem): return (x, y)
    return None
print('sizes |R| =', [len(r) for r in R], ' t = T/k =', round(T / k, 4), '< 6/7 =', round(6 / 7, 4))
print('pairwise |M_i & M_j|, |M_i & E,F,G,K|:', [[len(a & b) for b in M] for a in M], [[len(a & S) for S in (E, F, G, K)] for a in M])
print('{F,G,K,M1..M4} 2-transversal:', good([F, G, K] + M), '(None = good seven)')
print('{E,F,G,K,M1,M2,M3} 2-transversal (E-frame, for contrast):', good([E, F, G, K] + M[:3]))
