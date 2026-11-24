"""Exact rational re-simulation of a requester line against the mixed adversaries of prop.py / mix.py.

The float requests are snapped to rationals (a request within 3e-5 of the whole type (float drift over 6 rounds) becomes the whole type,
below 3e-5 becomes 0, others limit_denominator(10**6)).  No budget repair: the adversary's rule is applied with the TRUE unrequested
mass (reply = fraction 1/(N_e - |S_e|) of every unrequested class), and the line is checked to spend <= T.
Because lines found by the MILP at budget T' are knife-edge (some rounds request a union of whole types of
mass exactly T'), solve the MILP at T' = T - margin and verify here at T (argument 2 = margin).  The snapped line is a legal requester line; it is simulated with Fractions and the exact
min over kept 6-subsets of mass(D) - T is returned.  Rounding cannot decide anything: the number is exact for
the snapped line.  T and N are taken as the rationals closest to the floats (0.76 = 19/25, 2.0 = 2, ...).
Usage: py exact.py logfile   (reads the JSON lines written by prop.py / mix.py that contain "sol")."""
from fractions import Fraction as Fr
import json, sys
def popc(x): return bin(x).count("1")
ORD = {"LOW": lambda ty: sorted(ty, key=lambda J: (popc(J), J)),
       "HIGH": lambda ty: sorted(ty, key=lambda J: (-popc(J), J)),
       "GIFT": lambda ty: sorted(ty, key=lambda J: (J == 0, popc(J), J))}
def run(T, Ns, sol, alphas=None, order="LOW", margin=0):
    T = Fr(T).limit_denominator(10**4) + Fr(margin).limit_denominator(10**6); Ns = [Fr(x).limit_denominator(10**4) for x in Ns]
    E = len(Ns); m = {0: Ns[0] - 1, 1: Fr(1)}; real = {1}
    for e in range(1, E):
        b = 1 << e; m[0] += Ns[e] - Ns[e - 1]
        sf = sol[e - 1]; s = {}
        for J, mj in m.items():
            x = float(sf.get(str(J), sf.get(J, 0.0)))
            s[J] = mj if x >= float(mj) - 3e-5 else (Fr(0) if x < 3e-5 else Fr(x).limit_denominator(10**6))
        tot = sum(s.values())
        assert tot <= T and all(0 <= s[J] <= m[J] for J in s), f'over budget at round {e+1}: {float(tot)}'
        a = {J: m[J] - s[J] for J in m}
        slack = Ns[e] - tot - 1; lam = 1 / (Ns[e] - tot)   # rule with the TRUE unrequested mass
        al = Fr(1) if alphas is None else Fr(alphas[e - 1]).limit_denominator(1000)
        o_v = {J: Fr(0) for J in m}
        if al < 1:
            left = slack
            for J in ORD[order](sorted(m)):
                x = min(left, a[J]); o_v[J] = x; left -= x
            assert left == 0
        m2 = {}
        for J in m:
            o = al * (1 - lam) * a[J] + (1 - al) * o_v[J]
            m2[J] = s[J] + o
            if a[J] > 0:
                real.add(J | b)          # one unrequested point suffices (sliver)
                if a[J] - o > 0: m2[J | b] = a[J] - o
        m = m2
        assert sum(v for J, v in m.items() if J & b) == 1
    full = (1 << E) - 1
    cov7 = any((A | B) == full for A in real for B in real)
    best = None
    for drop in range(E):
        I = full & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        if best is None or D - T < best[0]: best = (D - T, drop + 1)
    return best[0], best[1], cov7
if __name__ == "__main__":
    for line in open(sys.argv[1]):
        if not line.startswith("{"): continue
        d = json.loads(line)
        if not d.get("sol"): continue
        al = d.get("alphas")
        mg = float(sys.argv[2]) if len(sys.argv) > 2 else 0.0
        z, drop, cov7 = run(d["T"], d["Ns"], d["sol"], al, d.get("order") or "LOW", mg)
        print(f"MILP budget {d['T']}, verified at T = {d['T']}+{mg}: Ns={d['Ns'][0]}..{d['Ns'][-1]} alphas={al} order={d.get('order')}: float z={d['z']:+.6f}  "
              f"EXACT z = {z} = {float(z):+.6f} (drop {drop}); 7 replies coverable: {cov7}", flush=True)
