"""§14 helper: exact replay of a requester strategy tree against the adaptive tilted spread, with requests CLIPPED to
availability (a request is a function of the bits already seen, so clipping to the realized masses is legitimate).
replay(T, N, bits, reqs) -> (min over 7 discards of mass(D) - T_exact, drop, unused budget).
Same rule as tilt.exact_leaf; the only change is s[J] = min(request, m[J])."""
from fractions import Fraction as Fr
import itertools, tilt
def replay(T, N, bits, reqs, margin=0.0):
    Tq = Fr(T).limit_denominator(10**4) + Fr(margin).limit_denominator(10**6); Nq = Fr(N).limit_denominator(10**4)
    m = {0: Nq - 1, 1: Fr(1)}; real = {1}; half = Fr(1, 2); unused = []
    for e in range(1, 7):
        b = 1 << e; sf = reqs[e - 1]; s = {}
        for J, mj in m.items():
            x = float(sf.get(J, sf.get(str(J), 0.0)))
            s[J] = mj if x >= float(mj) - 3e-5 else (Fr(0) if x < 3e-5 else Fr(x).limit_denominator(10**6))
        tot = sum(s.values()); assert tot <= Tq, f"over budget at reply {e+1}: {float(tot)}"
        unused.append(float(Tq - tot))
        a = {J: m[J] - s[J] for J in m}; slack = Nq - tot - 1; lam = 1 / (Nq - tot)
        ov = {J: Fr(0) for J in m}; left = slack
        for J in tilt.ORD[bits[e - 1]](sorted(m)):
            x = min(left, a[J]); ov[J] = x; left -= x
        assert left == 0
        m2 = {}
        for J in m:
            o = half * (1 - lam) * a[J] + half * ov[J]
            m2[J] = s[J] + o
            if a[J] > 0:
                real.add(J | b)
                if a[J] - o > 0: m2[J | b] = a[J] - o
        m = m2
    best = None
    for drop in range(7):
        I = 127 & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        if best is None or D - Tq < best[0]: best = (D - Tq, drop + 1)
    return best[0], best[1], max(unused)
def verify_tree(T, N, getreq, first="UO"):
    """getreq(prefix_string) -> request dict for the round after that prefix.  Returns list of (bits, margin, drop)."""
    out = []
    for rest in itertools.product("UO", repeat=5):
        for b0 in first:
            bits = (b0,) + rest
            reqs = [getreq("".join(bits[:e])) for e in range(6)]
            try: zq, d, un = replay(T, N, bits, reqs); out.append(("".join(bits), float(zq), d))
            except AssertionError as ex: out.append(("".join(bits), "error " + str(ex), None))
    return out
