r"""CORE 57: Theorem R (uniformly random selectors over arbitrary pool heads lose), numbers and a sanity simulation.
(a) [computed exact, log-binomials] F = frames around one head = C(k+T,T) C(T,k/2) C(k,k/2) / 6, the Chebyshev bound
    P(no head pencil) <= R^2/F + 9/C(k+T,T), and the exponent Phi/2 = lim log(F)/(2k); also the heterogeneous bound (1+3RD)R^2/F.
(b) [computed exact on samples] pool heads B_r (|B_r| = omega, random), sigma(S) uniform on R classes, reply S + B_r when S misses B_r:
    count requests triples forming a head pencil (three class-r requests on V - B_r, common intersection T - k/2, union V - B_r).
Usage: py random_selector.py
"""
import math, random, itertools
def lC(a, b): return math.lgamma(a + 1) - math.lgamma(b + 1) - math.lgamma(a - b + 1)
def h(x): return 0.0 if x <= 0 or x >= 1 else -x * math.log(x) - (1 - x) * math.log(1 - x)
print("(a) finite k: log F, Chebyshev bound at R = F^(1/2)/k (uniform), at R = (F/D)^(1/3)/k (heterogeneous)")
for k, T in [(8, 6), (40, 31), (100, 76), (400, 304), (4000, 3040)]:
    lF = lC(k + T, T) + lC(T, k // 2) + lC(k, k // 2) - math.log(6); lD = lC(T, k // 2) + lC(k, k // 2) - math.log(2)
    print(f"  k={k} T={T}: log F = {lF:.2f} (per k {lF/k:.4f}), log D/k = {lD/k:.4f}, 9/C(k+T,T) = {9*math.exp(-lC(k+T,T)):.2e}; "
          f"uniform: R < e^({lF/2/k:.4f} k); heterogeneous: R < e^({(lF-lD)/3/k:.4f} k)")
print("  first order: Phi(t)/2 and (Phi - d)/3 = log C(1+t,t)/3")
for t in (0.75, 0.76, 0.78, 0.8):
    Phi = (1 + t) * h(t / (1 + t)) + t * h(0.5 / t) + math.log(2)
    d = t * h(0.5 / t) + math.log(2)
    print(f"   t={t}: Phi = {Phi:.4f}, Phi/2 = {Phi/2:.4f}, (Phi-d)/3 = {(Phi-d)/3:.4f}")

def count_pencils(k, T, n, R, rng):
    om = n - k - T; V = list(range(n)); heads = [frozenset(rng.sample(V, om)) for _ in range(R)]
    sig = {S: rng.randrange(R) for S in itertools.combinations(V, T)}
    tot = 0; classes_with = 0
    for r in range(R):
        B = heads[r]; G = frozenset(V) - B
        A = set(frozenset(S) for S, c in sig.items() if c == r and not (B & set(S)))
        A_l = list(A); cnt = 0
        for i in range(len(A_l)):
            for j in range(i + 1, len(A_l)):
                I = A_l[i] & A_l[j]
                if len(I) != T - k // 2: continue
                S3 = (G - A_l[i] - A_l[j]) | I
                if len(S3) == T and S3 in A and S3 not in (A_l[i], A_l[j]): cnt += 1
        cnt //= 3; tot += cnt; classes_with += cnt > 0
    return tot, classes_with
print("(b) simulation (k,T,n)=(8,6,16): R, mean number of head pencils over 5 samples (first moment F/R^2), samples with none")
rng = random.Random(57)
for R in (16, 64, 256, 1024):
    res = [count_pencils(8, 6, 16, R, rng) for _ in range(5)]
    F = 525525
    print(f"  R={R}: pencils {[x for x, _ in res]} (F/R^2 = {F/R**2:.1f}); samples with no head pencil: {sum(1 for x, _ in res if x == 0)}/5", flush=True)
