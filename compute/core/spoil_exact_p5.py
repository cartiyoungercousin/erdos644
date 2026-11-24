"""CORE Part IX (60): EXACT check of the outer spoiler found by p5_strong.py at the five-reply position of positions/p5_level2.json.
Claim proved [Fractions]: with S = the stored request and dump D = {cell 123: a, cell 12345: om - a}, EVERY reading (every subset
of 2..6 of the six replies containing the new reply, every concurrency pattern) has need >= base = 1/10, and every old reading
(the five old replies) has need >= base.  Method: weak duality.  For a reading LP
  min sum u_e : per-type masses = mu, per-line load - u_e <= t, 0 <= u_e <= om, columns only for allowed incidence sets,
any z_e >= 0 gives the bound  sum_h y_h mu_h - t sum z_e + om sum_e min(0, 1 - z_e),  y_h = min over columns of h of sum_{e in E} z_e
(exactly dual feasible).  Float HiGHS proposes z (rationalised); the bound is recomputed in Fractions.
Usage: py spoil_exact_p5.py [a]   (a as rational string, default 131/1000)"""
import sys, json, itertools
from fractions import Fraction as Fr
import spoil as SP

def lower_bound(P, mu, t, om, z):
    rd = P.rd; r = rd.r; nF = len(rd.F)
    ymin = {}
    for hh, E in rd.cols:
        v = sum((z[e] for e in E), Fr(0))
        if hh not in ymin or v < ymin[hh]: ymin[hh] = v
    tot = Fr(0)
    for hh in range(1 << r):
        if mu[hh] > 0:
            if hh not in ymin: return None
            tot += ymin[hh] * mu[hh]
    tot -= t * sum(z, Fr(0))
    tot += om * sum((min(Fr(0), 1 - ze) for ze in z), Fr(0))
    return tot

def main(a):
    row = json.loads(open("positions/p5_level2.json").readline())
    t, N = Fr(19, 25), Fr(19, 10); om = N - 1 - t; base = om - 4 * (t - Fr(3, 4)); c = N - 1; nrep = row["nrep"]
    assert om == Fr(7, 50) and base == Fr(1, 10)
    pos = {int(J): Fr(v).limit_denominator(100000) for J, v in row["pos"].items()}
    s = {int(J): Fr(v).limit_denominator(100000) for J, v in row["s"].items()}
    assert sum(pos.values()) == N and sum(s.values()) == t and all(0 <= s.get(J, 0) <= pos[J] for J in s)
    for i in range(nrep): assert sum(v for J, v in pos.items() if J >> i & 1) == c
    d = {7: a, 31: om - a}
    for J, v in d.items(): assert 0 <= v <= pos[J] - s.get(J, 0), (J, v)
    bit = 1 << nrep; m2 = {}
    for J, v in pos.items():
        inn = s.get(J, Fr(0)) + d.get(J, Fr(0))
        if inn > 0: m2[J | bit] = m2.get(J | bit, Fr(0)) + inn
        if v - inn > 0: m2[J] = m2.get(J, Fr(0)) + v - inn
    for i in range(nrep + 1): assert sum(v for J, v in m2.items() if J >> i & 1) == c
    E = SP.Engine(float(t), float(N))
    res = {}
    for label, nr, new in (("new-reply readings", nrep + 1, nrep), ("old readings", nrep, None)):
        worst = None; cnt = 0; fails = []; nin = 0
        for (R, pi) in E.readings(nr, new=new):
            P = E.pats[len(R)][pi]; rd = P.rd
            mu_f = [0.0] * (1 << len(R)); mu = [Fr(0)] * (1 << len(R))
            for J, v in m2.items():
                hh = 0
                for i, x in enumerate(R):
                    if J >> x & 1: hh |= 1 << i
                mu[hh] += v
            val = P.need([float(x) for x in mu])
            if val >= SP.INF - 1e-9:   # LP infeasible: need = INF, claim holds vacuously
                cnt += 1; nin += 1; continue
            rowd = list(rd.h.getSolution().row_dual); nF = len(rd.F)
            best = None
            for sign in (1, -1):
                z = [Fr(sign * rowd[(1 << rd.r) + e]).limit_denominator(1000) for e in range(nF)]
                if any(x < 0 for x in z): continue
                b = lower_bound(P, mu, t, om, z)
                if b is not None and (best is None or b > best): best = b
            cnt += 1
            if best is None or best < base: fails.append((R, pi, float(val), None if best is None else str(best)))
            if best is not None and (worst is None or best < worst): worst = best
        res[label] = dict(readings=cnt, infeasible_in_float_only=nin, min_exact_lower_bound=str(worst), all_ge_base=not fails, fails=fails[:5])
    print(json.dumps(dict(a=str(a), base=str(base), **res), indent=1))

if __name__ == "__main__":
    main(Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(131, 1000))
