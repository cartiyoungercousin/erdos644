"""§14: tilt.add_leaf / replay generalized to R requested rounds (m = R + 2; R = 6 is tilt.py's m = 8, R = 7 is m = 9).
Same adversary rule; types are subsets of the R+1 replies; discard any one of the R+1 replies."""
import pulp
from fractions import Fraction as Fr
from tilt import ORD, AL
def add_leaf(prob, V, z, T, N, bits, fixed, drop, ref, R):
    E = R + 1; m = {0: N - 1.0, 1: 1.0}; rho = {1: 1}; hist = []
    slack = N - T - 1.0; lam = 1.0 / (N - T)
    for e in range(1, E):
        b = 1 << e; types = sorted(m); ub = {J: (1.0 if J else N) for J in types}
        if e - 1 < len(fixed): s = {J: float(fixed[e - 1].get(J, 0.0)) for J in types}
        else:
            s = {J: V(0, ub[J]) for J in types}
            for J in types: prob += s[J] <= m[J]
            prob += pulp.lpSum(s.values()) == T
            if ref is not None and e - 1 < len(ref):
                for J in ref[e - 1]:
                    if J in s: prob += s[J] - m[J] == 0
        a = {J: m[J] - s[J] for J in types}
        ov = {J: V(0, ub[J]) for J in types}
        for J in types: prob += ov[J] <= a[J]
        prob += pulp.lpSum(ov.values()) == slack
        pre = []
        for J in ORD[bits[e - 1]](types):
            pre.append(J); g = V(cat="Binary")
            prob += a[J] - ov[J] <= ub[J] * g
            prob += slack - pulp.lpSum(ov[K] for K in pre) <= slack * (1 - g)
        m2, rho2 = {}, dict(rho)
        for J in types:
            o = AL * (1 - lam) * a[J] + (1 - AL) * ov[J]
            m2[J] = s[J] + o; m2[J | b] = a[J] - o
            r = V(cat="Binary"); prob += a[J] <= ub[J] * r + 1e-7; rho2[J | b] = r
        hist.append(s); m, rho = m2, rho2
    full = (1 << E) - 1; I = full & ~(1 << (drop - 1)); delta = {}
    for P in range(full + 1):
        if P & ~I: continue
        comp = I & ~P
        if comp == 0: delta[P] = 1; continue
        dv = V(cat="Binary"); delta[P] = dv
        for K, rk in rho.items():
            if K and (K & comp) == comp:
                if isinstance(rk, int):
                    if rk: prob += dv >= 1
                else: prob += dv >= rk
    tot = []
    for J, mj in m.items():
        dl = delta[J & I]
        if isinstance(dl, int): tot.append(mj)
        else:
            d = V(0, N); prob += d >= mj - (N if J == 0 else 1.0) * (1 - dl); tot.append(d)
    prob += pulp.lpSum(tot) <= T + z
    return hist
def replay(T, N, bits, reqs, R):
    """exact replay at budget T (requests must sum to <= T), returns (min over discards of mass(D) - T, drop)"""
    Tq = Fr(T).limit_denominator(10**4); Nq = Fr(N).limit_denominator(10**4)
    m = {0: Nq - 1, 1: Fr(1)}; real = {1}; half = Fr(1, 2)
    for e in range(1, R + 1):
        b = 1 << e; sf = reqs[e - 1]; s = {}
        for J, mj in m.items():
            x = float(sf.get(J, 0.0))
            s[J] = mj if x >= float(mj) - 3e-5 else (Fr(0) if x < 3e-5 else Fr(x).limit_denominator(10**6))
        tot = sum(s.values()); assert tot <= Tq
        a = {J: m[J] - s[J] for J in m}; slack = Nq - tot - 1; lam = 1 / (Nq - tot)
        ov = {J: Fr(0) for J in m}; left = slack
        for J in ORD[bits[e - 1]](sorted(m)):
            x = min(left, a[J]); ov[J] = x; left -= x
        m2 = {}
        for J in m:
            o = half * (1 - lam) * a[J] + half * ov[J]
            m2[J] = s[J] + o
            if a[J] > 0:
                real.add(J | b)
                if a[J] - o > 0: m2[J | b] = a[J] - o
        m = m2
    full = (1 << (R + 1)) - 1; best = None
    for drop in range(R + 1):
        I = full & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        if best is None or D - Tq < best[0]: best = (D - Tq, drop + 1)
    return best
