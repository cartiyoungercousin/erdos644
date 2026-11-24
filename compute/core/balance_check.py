# CORE 14.1 balance lemma: exact pair, triangle-type request with a* points in each private part.
# Theorem T closes iff (almost) all of the dump lies outside K_1 ∪ K_2.   py balance_check.py
k, T, N = 100, 76, 189
c = N - k; om = c - T; a = N // 2 - 5 * k // 8 if N % 2 == 0 else (2 * N - 5 * k // 2) // 4   # a* = N/2 - 5k/8
a = 32
V = list(range(N))
O = set(range(0, a)); A = set(range(a, c)); B = set(range(c, 2 * c - a)); g = set(range(2 * c - a, N))
K1, K2 = O | A, O | B
sg = T - 2 * a
S = set(sorted(A)[:a]) | set(sorted(B)[:a]) | set(sorted(g)[:sg])
def tri_excess(K1, K2, K3):
    aa = (K1 & K2) - K3; b = (K1 & K3) - K2; d = (K2 & K3) - K1
    e1 = K1 - K2 - K3; e2 = K2 - K1 - K3; e3 = K3 - K1 - K2
    gg = set(V) - K1 - K2 - K3; ka = len(K1 & K2 & K3)
    base = [len(aa) + len(e3) + len(gg), len(b) + len(e2) + len(gg), len(d) + len(e1) + len(gg)]
    best = min(max(base[0] + x, base[1] + y, base[2] + ka - x - y) for x in range(ka + 1) for y in range(ka + 1 - x))
    return max(best, len(e1) + len(e2) + len(e3)) - T
print("k,T,N =", k, T, N, " c =", c, " omega =", om, " a* =", a, " |g| =", len(g), " eps*k =", T - 3 * k // 4)
freeO, freeA, freeB, freeg = sorted(O - S), sorted(A - S), sorted(B - S), sorted(g - S)
for (dO, dA, dB) in [(0,0,0), (1,0,0), (0,1,0), (0,1,1), (2,0,0), (0,2,0), (0,2,2), (3,0,0), (0,0,5), (13,0,0), (0,13,0), (0,6,7)]:
    D = set(freeO[:dO]) | set(freeA[:dA]) | set(freeB[:dB]) | set(freeg[:om - dO - dA - dB])
    print("  dump (O, A, B, g) = (%2d,%2d,%2d,%2d): Theorem-T excess %3d  -> %s"
          % (dO, dA, dB, om - dO - dA - dB, tri_excess(K1, K2, S | D), "WIN" if tri_excess(K1, K2, S | D) <= 0 else "no"))
