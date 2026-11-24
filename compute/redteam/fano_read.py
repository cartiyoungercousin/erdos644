"""RED TEAM §11: read off what a saved winning requester line realises at the end (analysis only, no search).
For a logged line (prop.py / mix.py / nb.py JSON with "sol"): re-simulate, take the six kept replies plus the
eighth reply (any k-set avoiding D), list final type masses, the empty triples, every Fano labelling of the seven
for which all realised types are line-free (30 labelled Fano planes checked exhaustively), its class by the first
four kept rounds ((L) collinear triple first, (T) triangle + point on a side, (Q) quadrangle), and per round the
Fano block M_c (mass, and how much of the request it is).
Usage: py fano_read.py logfile [index]"""
import json, sys, itertools
def popc(x): return bin(x).count("1")
ORD = {"LOW": lambda ty: sorted(ty, key=lambda J: (popc(J), J)),
       "HIGH": lambda ty: sorted(ty, key=lambda J: (-popc(J), J)),
       "GIFT": lambda ty: sorted(ty, key=lambda J: (J == 0, popc(J), J))}
STD = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
def planes():
    out = set()
    for p in itertools.permutations(range(7)):
        out.add(frozenset(frozenset(p[i] for i in l) for l in STD))
    return [sorted(tuple(sorted(l)) for l in pl) for pl in out]
PLANES = planes()
def simulate(d, eps=2e-6):
    T, Ns, sol = d["T"], d["Ns"], d["sol"]; al = d.get("alphas") or [1.0] * 6; order = d.get("order") or "LOW"
    E = 7; m = {0: Ns[0] - 1.0, 1: 1.0}; real = {1}; hist = []
    for e in range(1, E):
        b = 1 << e; s = {int(J): v for J, v in sol[e - 1].items()}; tot = sum(s.values()); lam = 1 / (Ns[e] - tot); slack = Ns[e] - tot - 1
        a = {J: m[J] - min(m[J], s.get(J, 0.0)) for J in m}
        ov = {J: 0.0 for J in m}; left = slack
        if al[e - 1] < 1:
            for J in ORD[order](sorted(m)):
                x = min(left, a[J]); ov[J] = x; left -= x
        hist.append((dict(m), {J: m[J] - a[J] for J in m}))
        m2 = {}
        for J in m:
            o = al[e - 1] * (1 - lam) * a[J] + (1 - al[e - 1]) * ov[J]
            m2[J] = m[J] - a[J] + o
            if a[J] > eps:
                real.add(J | b)
                if a[J] - o > eps: m2[J | b] = a[J] - o
        m = {J: v for J, v in m2.items() if v > eps or J == 0}
    return m, real, hist
def ts(J, names): return "".join(names[i] for i in range(len(names)) if (J >> i) & 1) or "-"
def report(d):
    m, real, hist = simulate(d); E = 7; full = 127; drop = d["drop"][0] - 1
    kept = [i for i in range(E) if i != drop]                      # original indices, time order
    I = full & ~(1 << drop)
    pos = {i: n for n, i in enumerate(kept)}                       # kept index 0..5 ; the eighth reply = 6
    def proj(J): return sum(1 << pos[i] for i in kept if (J >> i) & 1)
    names = [str(i + 1) for i in kept] + ["8"]
    mass = {}
    for J, v in m.items(): mass[proj(J)] = mass.get(proj(J), 0.0) + v
    r6 = {proj(K) for K in real}
    inD = lambda J: any((K & (63 & ~J)) == (63 & ~J) for K in r6)
    Dm = sum(v for J, v in mass.items() if inD(J))
    r7 = set(r6) | {J | 64 for J, v in mass.items() if v > 2e-6 and not inD(J)} | {64}
    print(f"=== N={d['Ns'][0]} t(budget)={d['T']} alphas={d.get('alphas')} order={d.get('order')} discard reply {drop + 1}; kept replies {names[:6]} + final reply 8;  mass(D)={Dm:.4f}")
    for deg in range(7):
        tt = sorted(((J, v) for J, v in mass.items() if popc(J) == deg and v > 5e-4), key=lambda x: -x[1])
        if tt: print(f"  degree {deg} (mass {sum(v for _, v in tt):.4f}; in D {sum(v for J, v in tt if inD(J)):.4f}): " + "  ".join(f"{ts(J, names)}={v:.3f}{'*' if inD(J) else ''}" for J, v in tt))
    faces = {S for S in range(128) if any((K & S) == S for K in r7)}
    emp = [S for S in range(128) if popc(S) == 3 and S not in faces]
    print(f"  empty triples among the seven ({len(emp)} of 35): " + " ".join(ts(S, names) for S in emp))
    print(f"  realised 4-fold types: " + " ".join(ts(K, names) for K in sorted(r7) if popc(K) == 4) + f" ; 5-fold or more: {sum(1 for K in r7 if popc(K) >= 5)}")
    good = []
    for pl in PLANES:
        lm = [sum(1 << i for i in l) for l in pl]
        if all(all((K & L) != L for L in lm) for K in r7): good.append(pl)
    print(f"  Fano labellings with every realised type line-free: {len(good)} of 30")
    for pl in good:
        lm = [sum(1 << i for i in l) for l in pl]
        coll = lambda a, b, c: any(L == (1 << a | 1 << b | 1 << c) for L in lm)
        if coll(0, 1, 2): cls = "(L) line-first"
        elif any(coll(a, b, 3) for a, b in ((0, 1), (0, 2), (1, 2))): cls = "(T) triangle + point on a side"
        else: cls = "(Q) quadrangle-first"
        print(f"    lines {' '.join(ts(L, names) for L in lm)}   class by the first four kept rounds: {cls}")
        # blocks: at kept round c (kept index n >= 2), M_c = points whose kept type J (earlier kept only) has a line {a,b,c}, a,b in J
        for n in range(2, 7):
            if n < 6:
                e = kept[n]; mm, ss = hist[e - 1]
            else:
                mm = m; ss = None
            blk = 0.0; req = 0.0; tot = 0.0 if ss is None else sum(ss.values()); parts = {}
            for J, v in mm.items():
                Jp = sum(1 << pos[i] for i in kept if (J >> i) & 1 and pos[i] < n)
                hit = [L for L in lm if (L >> n) & 1 and popc(L & Jp) == 2]
                if hit and v > 1e-9:
                    blk += v; req += (ss.get(J, 0.0) if ss is not None else v)
                    key = ts(Jp, names); parts[key] = parts.get(key, 0.0) + v
            top = " ".join(f"{a}:{b:.3f}" for a, b in sorted(parts.items(), key=lambda x: -x[1])[:8])
            if ss is not None:
                print(f"      reply {names[n]}: block M mass {blk:.4f}, of which requested {req:.4f}; whole request {tot:.4f} (free part {tot - req:.4f})   block types: {top}")
            else:
                print(f"      reply 8 (final): block M mass {blk:.4f} (= D restricted to this labelling; true D {Dm:.4f})   block types: {top}")
    return len(good)
if __name__ == "__main__":
    recs = [json.loads(l) for l in open(sys.argv[1]) if l.startswith("{")]
    recs = [d for d in recs if d.get("sol") and d.get("z") is not None and d["z"] < 0]
    if len(sys.argv) > 2: recs = [recs[int(sys.argv[2])]]
    for d in recs: report(d)
