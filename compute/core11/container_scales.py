r"""CORE 85-86: container codegree check at the sparse scale.  [computed float]
Host X = all co-edges (c-subsets of V, |V| = Nk), log|X| = N h(1/N) per k.  The host is vertex-transitive under Sym(V),
so Saxton-Thomason's delta_j equals Delta_j / d exactly.
Scale: tau = p = e^{-gamma k} (fingerprint no larger than the sparsest T-covering family) and eps = p^r e^{-eta k}
(supersaturation cannot exceed the edge density of the random threshold family, which is T-covering).
ST condition delta_j <= eps tau^{j-1} (constants dropped: subexponential) becomes, per k,
      L_j := log(d / Delta_j) >= (r + j - 1) gamma + eta     for all 2 <= j <= r.
Delta_j is bounded BELOW by the codegree of a typical j-subset of a dominant-shape edge, so L_j(typ) is an UPPER bound
on L_j, and L_j(typ) < (r+j-1) gamma shows (at first order) that the condition fails.  For pencils L_2 is a true max.
Columns: eps* = min_j [L_j - (j-1) gamma] = best achievable -log(eps)/k at tau = p ; need = r gamma.
"""
import math, itertools


def h(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log(x) - (1 - x) * math.log(1 - x)


def H(ws):
    s = sum(ws)
    return -sum(w / s * math.log(w / s) for w in ws if w > 0)


def ent_mass(ms):  # log multinomial per k of a partition with masses ms
    N = sum(ms)
    return N * H(ms) if N > 0 else 0.0


# ---------- Fano sevens ----------
LINES = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
TYPES = [I for m in range(1, 128) for I in [frozenset(i for i in range(7) if m >> i & 1)]
         if any(set(l) <= I for l in LINES)]


def seven(N, c):
    lo, hi = 1e-9, 1e9
    for _ in range(200):
        x = math.sqrt(lo * hi)
        w = [x ** len(I) for I in TYPES]
        m = sum(len(I) * wi for I, wi in zip(TYPES, w)) / sum(w)
        if m < 7 * c / N:
            lo = x
        else:
            hi = x
    Z = sum(w)
    P = {I: wi / Z for I, wi in zip(TYPES, w)}
    HP = -sum(q * math.log(q) for q in P.values())
    out = {}
    for j in range(2, 8):
        best = None
        for J in itertools.combinations(range(7), j):
            marg = {}
            for I, q in P.items():
                key = I & frozenset(J)
                marg[key] = marg.get(key, 0) + q
            HJ = -sum(q * math.log(q) for q in marg.values() if q > 0)
            L = N * (HJ - h(1 / N))
            best = L if best is None else min(best, L)  # worst J = largest codegree
        out[j] = best
    return N * HP, out


# ---------- pencils: union V, triple intersection kap in [N-2t, N-3/2] ----------
def pencil(N, c, t):
    K = [N - 2 * t + i * ((N - 1.5) - (N - 2 * t)) / 200 for i in range(201)]
    best = None
    for kap in K:
        p = 2 * N - 3 - 2 * kap
        s = 3 - N + kap
        if p < -1e-12 or s < -1e-12:
            continue
        e = ent_mass([kap] + [p / 3] * 3 + [s / 3] * 3)
        if best is None or e > best[0]:
            best = (e, kap)
    eG = best[0]
    # Delta_2: max over positions of K1,K2 of #K3: K3 contains V\(K1 u K2), meets K1nK2 in kap,
    # K1\K2 in p13, K2\K1 in p23, with p12 + p13 + p23 = 2N-3-2kap; K1nK2 = kap + p12.
    D2 = None
    for kap in K:
        P = 2 * N - 3 - 2 * kap
        for i in range(81):
            p12 = P * i / 80
            rest = P - p12
            a = c - kap - p12
            if a < -1e-12:
                continue
            for jj in range(41):
                p13 = rest * jj / 40
                p23 = rest - p13
                if p13 > a + 1e-12 or p23 > a + 1e-12:
                    continue
                v = ent_mass([kap, p12]) + ent_mass([p13, max(a - p13, 0)]) + ent_mass([p23, max(a - p23, 0)])
                D2 = v if D2 is None else max(D2, v)
    return eG, D2


# ---------- Theorem-T triangles (kappa split evenly; symmetric maxent) ----------
def triangle(N, c, t):
    best = None
    for i in range(1, 300):
        for j in range(0, 300):
            kap = max(N - 1.5, 0) * j / 299
            e = t / 3 * i / 300
            a = (c - kap - e) / 2
            g = N - kap - 3 * a - 3 * e
            if a < 0 or g < -1e-12:
                continue
            if a + e + g + kap / 3 > t + 1e-12:
                continue
            v = ent_mass([kap] + [a] * 3 + [e] * 3 + [max(g, 0)])
            if best is None or v > best[0]:
                best = (v, a, e, g, kap)
    if best is None:
        return None
    v, a, e, g, kap = best
    m2 = [kap + a, a + e, a + e, e + g]  # in both / only K1 / only K2 / neither
    L2 = ent_mass(m2) - N * h(1 / N)
    L3 = v - N * h(1 / N)
    return v, L2, L3, best


# ---------- Q' quadruples, S4-symmetric maxent ----------
def quad(N, c, t):
    best = None
    G = 50
    smax = (3 * t - N) / 2
    for i0 in range(G + 1):
        for i2 in range(G + 1):
            for i4 in range(G + 1):
                m0 = smax * i0 / G
                m2 = (t / 2) * i2 / G
                m4 = max(N - 1.5, 0) * i4 / G
                A = (N - m0 - 6 * m2 - m4) / 4  # m1 + m3
                B = c - 3 * m2 - m4             # m1 + 3 m3
                m3 = (B - A) / 2
                m1 = A - m3
                if min(m1, m3) < -1e-12:
                    continue
                sig = m0 + 4 * m1
                if sig > smax + 1e-12 or 2 * m2 + sig > t + 1e-12:
                    continue
                ms = [m0] + [m1] * 4 + [m2] * 6 + [m3] * 4 + [m4]
                v = ent_mass([max(x, 0) for x in ms])
                if best is None or v > best[0]:
                    best = (v, m0, m1, m2, m3, m4)
    if best is None:
        return None
    v, m0, m1, m2, m3, m4 = best
    Ls = {}
    for j in (2, 3):
        marg = {}
        for mask in range(16):
            I = frozenset(i for i in range(4) if mask >> i & 1)
            w = max([m0, m1, m2, m3, m4][len(I)], 0)
            key = I & frozenset(range(j))
            marg[key] = marg.get(key, 0) + w
        Ls[j] = ent_mass(list(marg.values())) - N * h(1 / N)
    Ls[4] = v - N * h(1 / N)
    return v, Ls, best


if __name__ == '__main__':
 for t in (0.7501, 0.76, 0.78):
     print(f"\n==== t = {t} ====")
     lo, hi = 3 * t - 0.5, 3 - t
     for i in range(1, 10, 2):
         N = lo + (hi - lo) * i / 10
         c = N - 1
         om = c - t
         g = (N - t) * h(om / (N - t))
         LX = N * h(1 / N)
         print(f"N={N:.4f} gamma={g:.4f} log|X|={LX:.4f} log|I_min|={LX - g:.4f}")
         eG, L = seven(N, c)
         eps7 = min(L[j] - (j - 1) * g for j in L)
         worst = min(L, key=lambda j: L[j] - (j - 1) * g)
         print(f"  sevens  r=7 log e={eG:.4f} sev={eG - 7 * g:+.4f} L_j(typ)=" + " ".join(f"{L[j]:.3f}" for j in range(2, 8))
               + f" | eps*<={eps7:.4f} need 7g={7 * g:.4f} margin<={eps7 - 7 * g:+.4f} (worst j={worst})")
         eP, D2 = pencil(N, c, t)
         L2 = eP - LX - D2
         L3 = eP - LX
         epsP = min(L2 - g, L3 - 2 * g)
         print(f"  pencils r=3 log e={eP:.4f} L_2={L2:.4f} L_3={L3:.4f} | eps*={epsP:.4f} need 3g={3 * g:.4f} margin={epsP - 3 * g:+.4f}")
         tr = triangle(N, c, t)
         if tr:
             v, L2t, L3t, b = tr
             epsT = min(L2t - g, L3t - 2 * g)
             print(f"  triang. r=3 log e={v:.4f} L_2(typ)={L2t:.4f} L_3={L3t:.4f} | eps*<={epsT:.4f} need 3g={3 * g:.4f} margin<={epsT - 3 * g:+.4f}")
         else:
             print("  triang. none")
         q = quad(N, c, t)
         if q:
             v, Ls, b = q
             epsQ = min(Ls[j] - (j - 1) * g for j in Ls)
             print(f"  Q'quad  r=4 log e={v:.4f} L_j(typ)=" + " ".join(f"{Ls[j]:.3f}" for j in (2, 3, 4))
                   + f" | eps*<={epsQ:.4f} need 4g={4 * g:.4f} margin<={epsQ - 4 * g:+.4f}")
         else:
             print("  Q'quad  none feasible")
