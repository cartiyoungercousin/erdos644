"""§17: exact rational replay of the TYPE-RELATIVE tree (phi rule) against a mode sequence. usage: py multimode_rel_replay.py "U0.5,P,..." [-v]"""
import sys, json
from fractions import Fraction as Fr
from multimode_replay import ORD
T = Fr(76, 100); N = Fr(18, 10); import os
FILL = Fr(os.environ.get('FILL', '0')).limit_denominator(10**6) if os.environ.get('FILL') else None
PHI = json.load(open("logs/phi_rule.json"))
def reply_r(m, a, tot, md):
    f = Fr(md[1:]) if md != "P" else Fr(0); o_ = "U" if md == "P" else md[0]
    slack = N - tot - 1; lam = 1 / (N - tot); ov = {J: Fr(0) for J in m}; left = slack
    for J in ORD[o_](sorted(m)):
        x = min(left, a[J]); ov[J] = x; left -= x
    assert left == 0
    return {J: a[J] - ((1 - f) * (1 - lam) * a[J] + f * ov[J]) for J in m}
def replay(seq, verbose=False):
    m = {0: N - 1, 1: Fr(1)}; real = {1}; lab = ""
    for e in range(1, 7):
        b = 1 << e; ph = PHI[lab]; s = {J: Fr(0) for J in m}; C = P = Fr(0)
        for J, mj in m.items():
            p = ph.get(str(J))
            if not p or mj <= 0: continue
            if p >= 1: s[J] = mj; C += mj
            else: s[J] = Fr(p).limit_denominator(10**9) * mj; P += s[J]
        if C + P > T:
            if C < T:
                for J in s:
                    if ph.get(str(J), 1) < 1: s[J] *= (T - C) / P
            else:
                for J in s:
                    if ph.get(str(J), 1) < 1: s[J] = Fr(0)
                t = C
                for J in sorted([J for J in s if s[J] > 0], key=lambda J: m[J]):
                    if t <= T: break
                    t -= s[J]; s[J] = Fr(0)
        if FILL:
            left = Fr(FILL) - sum(s.values())
            if left > Fr(1, 10**9):
                for J in sorted([J for J in m if m[J] - s[J] > Fr(1, 10**9)], key=lambda J: (m[J] - s[J]) if os.environ.get('ASC') == '1' else -(m[J] - s[J])):
                    if left <= 0: break
                    x = min(left, m[J] - s[J]); s[J] += x; left -= x
        tot = sum(s.values()); assert tot <= T
        a = {J: m[J] - s[J] for J in m}
        r = reply_r(m, a, tot, seq[e - 1])
        rU = reply_r(m, a, tot, "U0.5"); rO = reply_r(m, a, tot, "O0.5")
        dU = sum(abs(r[J] - rU[J]) for J in m); dO = sum(abs(r[J] - rO[J]) for J in m)
        lab += "U" if dU <= dO else "O"
        m2 = {}
        for J in m:
            m2[J] = m[J] - r[J]
            if a[J] > 0:
                real.add(J | b)
                if r[J] > 0: m2[J | b] = r[J]
        m = m2
    best = None
    for drop in range(7):
        I = 127 & ~(1 << drop)
        inD = {J: mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real)}
        D = sum(inD.values())
        if best is None or D - T < best[0]: best = (D - T, drop + 1, inD)
    if verbose:
        z, d, inD = best
        print("labels", lab, "best discard", d)
        for J, v in sorted(inD.items(), key=lambda t: -t[1])[:8]: print("  in D: type", J, bin(J), "mass %.4f" % float(v))
        print("  total mass in D %.4f, not in D: %s" % (float(sum(inD.values())), {J: round(float(v), 4) for J, v in m.items() if J not in inD and v > 1e-4}))
    return best[0], best[1], lab
if __name__ == "__main__":
    z, d, lab = replay(sys.argv[1].split(","), "-v" in sys.argv)
    print(sys.argv[1], "labels", lab, "margin mass(D)-T = %.6f (discard %d)" % (float(z), d), "ADVERSARY BEATS rel tree" if z > 0 else "requester wins")
