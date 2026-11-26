"""§15: does a winning tree HEDGE across the adversary's bits?  For every leaf: the plan actually played (per round, the
set of types requested completely, s = m in exact replay), and the set of discards that win (mass(D) < T).
Reports how many distinct full-request patterns and winning-discard sets occur, and which bit positions they depend on.
Usage: py adaptive_hedge.py T N R treefile"""
import sys, json, itertools
from fractions import Fraction as Fr
import tilt


def leaf(T, N, R, bits, reqs):
    Tq = Fr(T).limit_denominator(10**4); Nq = Fr(N).limit_denominator(10**4)
    m = {0: Nq - 1, 1: Fr(1)}; real = {1}; half = Fr(1, 2); pat = []
    for e in range(1, R + 1):
        b = 1 << e; sf = reqs[e - 1]; s = {}
        for J, mj in m.items():
            x = float(sf.get(J, 0.0))
            s[J] = mj if x >= float(mj) - 3e-5 else (Fr(0) if x < 3e-5 else Fr(x).limit_denominator(10**6))
        pat.append(tuple(sorted(J for J in m if m[J] > 0 and s[J] == m[J])))
        tot = sum(s.values()); a = {J: m[J] - s[J] for J in m}; slack = Nq - tot - 1; lam = 1 / (Nq - tot)
        ov = {J: Fr(0) for J in m}; left = slack
        for J in tilt.ORD[bits[e - 1]](sorted(m)):
            x = min(left, a[J]); ov[J] = x; left -= x
        m2 = {}
        for J in m:
            o = half * (1 - lam) * a[J] + half * ov[J]
            m2[J] = s[J] + o
            if a[J] > 0:
                real.add(J | b)
                if a[J] - o > 0: m2[J | b] = a[J] - o
        m = m2
    full = (1 << (R + 1)) - 1; wins = []
    for drop in range(R + 1):
        I = full & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        if D < Tq: wins.append(drop + 1)
    return tuple(pat), tuple(wins)


def main(T, N, R, tf):
    tree = {k: {int(J): v for J, v in r.items()} for k, r in json.load(open(tf)).items()}
    rows = {}
    for bits in itertools.product("UO", repeat=R):
        b = "".join(bits); rows[b] = leaf(T, N, R, b, [tree[b[:e]] for e in range(R)])
    pats = sorted({p for p, _ in rows.values()}); wins = sorted({w for _, w in rows.values()})
    # which bit positions does the full-request pattern of round e depend on?
    dep = {}
    for e in range(R):
        d = []
        for i in range(e):
            for b in rows:
                b2 = b[:i] + ("O" if b[i] == "U" else "U") + b[i + 1:]
                if rows[b][0][e] != rows[b2][0][e]: d.append(i + 2); break
        dep[f"reply{e + 2}_request"] = d
    out = dict(T=T, N=N, m=R + 2, leaves=len(rows), distinct_full_request_patterns=len(pats),
               winning_discard_sets={str(w): sum(1 for _, x in rows.values() if x == w) for w in wins},
               pattern_depends_on_bits_of_replies=dep,
               single_common_discard=sorted(set.intersection(*[set(w) for _, w in rows.values()])))
    return out


if __name__ == "__main__":
    print(json.dumps(main(float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), sys.argv[4])))
