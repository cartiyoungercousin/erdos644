"""Print the terminal position of a logged requester line (prop.py / mix.py JSON with "sol"): degree profile of the
six kept replies, the realized nerve by face size, and which template the position resembles.
Usage: py show.py logfile [line_index]"""
import json, sys
def popc(x): return bin(x).count("1")
ORD = {"LOW": lambda ty: sorted(ty, key=lambda J: (popc(J), J)),
       "HIGH": lambda ty: sorted(ty, key=lambda J: (-popc(J), J)),
       "GIFT": lambda ty: sorted(ty, key=lambda J: (J == 0, popc(J), J))}
def final(d, eps=2e-6):
    T, Ns, sol = d["T"], d["Ns"], d["sol"]; al = d.get("alphas") or [1.0] * 6; order = d.get("order") or "LOW"
    E = len(Ns); m = {0: Ns[0] - 1.0, 1: 1.0}; real = {1}
    for e in range(1, E):
        b = 1 << e; m[0] += Ns[e] - Ns[e - 1]; s = {int(J): v for J, v in sol[e - 1].items()}
        tot = sum(s.values()); lam = 1 / (Ns[e] - tot); slack = Ns[e] - tot - 1
        a = {J: m[J] - min(m[J], s.get(J, 0.0)) for J in m}
        ov = {J: 0.0 for J in m}; left = slack
        if al[e - 1] < 1:
            for J in ORD[order](sorted(m)):
                x = min(left, a[J]); ov[J] = x; left -= x
        m2 = {}
        for J in m:
            o = al[e - 1] * (1 - lam) * a[J] + (1 - al[e - 1]) * ov[J]
            m2[J] = m[J] - a[J] + o
            if a[J] > eps:
                real.add(J | b)
                if a[J] - o > eps: m2[J | b] = a[J] - o
        m = {J: v for J, v in m2.items() if v > eps or J == 0}
    return m, real
if __name__ == "__main__":
    lines = [json.loads(l) for l in open(sys.argv[1]) if l.startswith("{")]
    d = lines[int(sys.argv[2]) if len(sys.argv) > 2 else 0]
    m, real = final(d); E = 7; full = (1 << E) - 1; drop = d["drop"][0] - 1; I = full & ~(1 << drop)
    proj = {}
    for J, v in m.items(): proj[J & I] = proj.get(J & I, 0.0) + v
    rproj = {K & I for K in real}
    inD = lambda J: any((K & (I & ~J)) == (I & ~J) for K in rproj)
    ts = lambda J: "".join(str(i + 1) for i in range(E) if (J >> i) & 1) or "-"
    print(f"T={d['T']} N={d['Ns'][0]}..{d['Ns'][-1]} alphas={d.get('alphas')} z={d['z']:+.4f} kept = all but reply {drop + 1}")
    for deg in range(7):
        tt = [(J, v) for J, v in proj.items() if popc(J) == deg and v > 1e-6]
        if tt: print(f"  degree {deg}: mass {sum(v for _, v in tt):.4f} in {len(tt)} heavy types; in D: {sum(v for J, v in tt if inD(J)):.4f}   "
                     + " ".join(f"{ts(J)}:{v:.3f}{'*' if inD(J) else ''}" for J, v in sorted(tt, key=lambda x: -x[1])[:10]))
    print("  realized faces by size (among kept six):", {k: len({K for K in rproj if popc(K) == k}) for k in range(1, 7)})
    print("  mass(D) =", round(sum(v for J, v in proj.items() if inD(J)), 6))
