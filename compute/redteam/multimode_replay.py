"""§16: exact rational replay of a multi-mode reply sequence against the fixed §14 tree.
usage: py multimode_replay.py "U0.5,U0.75,O0.5,..." bits [TAU]   (bits = mapped U/O path used to look up her requests)"""
import sys, json
from fractions import Fraction as Fr
def popc(x): return bin(x).count("1")
ORD = {"U": lambda ty: sorted(ty, key=lambda J: (popc(J), J)), "O": lambda ty: sorted(ty, key=lambda J: (-popc(J), J)),
       "G": lambda ty: sorted(ty, key=lambda J: (J == 0, popc(J), J)), "P": lambda ty: sorted(ty)}
def replay(seq, bits, T=Fr(76, 100), N=Fr(18, 10), tau=Fr(0), tree=None):
    tree = tree or json.load(open("logs/adaptive_tree_full_T0.76_N1.8.json"))
    m = {0: N - 1, 1: Fr(1)}; real = {1}; log = []
    for e in range(1, 7):
        b = 1 << e; sf = tree[bits[:e - 1]]; s = {}
        for J, mj in m.items():
            x = float(sf.get(str(J), 0.0))
            xq = Fr(x).limit_denominator(10**6)
            if x >= float(mj) - 3e-5 or (tau > 0 and x >= 3e-5 and mj <= xq + tau): s[J] = mj
            else: s[J] = Fr(0) if x < 3e-5 else xq
        tot = sum(s.values()); assert tot <= T, f"over budget round {e}: {float(tot)}"
        a = {J: m[J] - s[J] for J in m}; slack = N - tot - 1; lam = 1 / (N - tot)
        md = seq[e - 1]; f = Fr(md[1:]) if md != "P" else Fr(0); o_ = "U" if md == "P" else md[0]
        ov = {J: Fr(0) for J in m}; left = slack
        for J in ORD[o_](sorted(m)):
            x = min(left, a[J]); ov[J] = x; left -= x
        assert left == 0
        m2 = {}
        for J in m:
            o = (1 - f) * (1 - lam) * a[J] + f * ov[J]
            m2[J] = s[J] + o
            if a[J] > 0:
                real.add(J | b)
                if a[J] - o > 0: m2[J | b] = a[J] - o
        m = m2
        assert sum(v for J, v in m.items() if J & b) == 1 and sum(m.values()) == N
    best = None
    for drop in range(7):
        I = 127 & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        if best is None or D - T < best[0]: best = (D - T, drop + 1)
    return best
if __name__ == "__main__":
    seq = sys.argv[1].split(","); bits = sys.argv[2]; tau = Fr(sys.argv[3]) if len(sys.argv) > 3 else Fr(0)
    z, d = replay(seq, bits, tau=tau)
    print(sys.argv[1], bits, "tau", float(tau), "margin mass(D)-T = %.6f (discard %d)" % (float(z), d), "ADVERSARY BEATS FIXED TREE" if z > 0 else "requester wins")
