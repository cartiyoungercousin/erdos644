"""Try every logged winning line (nb_*.log, cert) as a PLAN (types requested completely per round + its discard)
against a target adversary of the mix.py family; MILP re-optimises the rest; exact verification at T = 0.76.
Usage: py planall.py alphas order [N] [tl]"""
import sys, json, glob, mix, exact
al = [float(x) for x in sys.argv[1].split(",")]; al = al * 6 if len(al) == 1 else al
order = sys.argv[2]; N = float(sys.argv[3]) if len(sys.argv) > 3 else 2.0; tl = float(sys.argv[4]) if len(sys.argv) > 4 else 40
refs = []
for f in ["cert_N2_T076.json"] + sorted(glob.glob("nb_[01].log")) + ["plan.log"]:
    for l in open(f):
        if not l.startswith("{"): continue
        d = json.loads(l)
        if d.get("sol") and d.get("z") is not None and d["z"] < -0.002 and abs(d["Ns"][0] - N) < 1e-9: refs.append((f, d))
best = None
for f, d in refs:
    ral = d.get("alphas") or [1.0] * 6; rord = d.get("order") or "LOW"
    E = 7; m = {0: N - 1.0, 1: 1.0}; ref = []
    for e in range(1, E):
        b = 1 << e; s = {int(J): v for J, v in d["sol"][e - 1].items()}; tot = sum(s.values()); lam = 1 / (N - tot); slack = N - tot - 1
        a = {J: m[J] - min(m[J], s.get(J, 0.0)) for J in m}
        ref.append({J for J in m if m[J] > 2e-6 and a[J] < 2e-6})
        ov = {J: 0.0 for J in m}; left = slack
        if ral[e - 1] < 1:
            for J in mix.ORD[rord](sorted(m)):
                x = min(left, a[J]); ov[J] = x; left -= x
        m2 = {}
        for J in m:
            o = ral[e - 1] * (1 - lam) * a[J] + (1 - ral[e - 1]) * ov[J]; m2[J] = m[J] - a[J] + o
            if a[J] > 2e-6: m2[J | b] = a[J] - o
        m = m2
    st, zv, dr, bd, sol = mix.solve(0.759, [N] * 7, al, order, tl, d["drop"], ref=ref)
    ze = None
    if zv is not None and zv < -0.0015:
        try: ze = float(exact.run(0.759, [N] * 7, sol, al, order, 0.001)[0])
        except AssertionError as ex: ze = "err"
    print(f"  plan from {f} alphas={ral} {rord} drop {d['drop']}: {st} z={zv} exact_at_T={ze}", flush=True)
    if zv is not None and (best is None or zv < best[0]): best = (zv, ze, ral, rord, d["drop"])
print(json.dumps(dict(target_alphas=al, order=order, N=N, best_z=best[0] if best else None, best_exact=best[1] if best else None,
                      plan=str(best[2:]) if best else None, nplans=len(refs))), flush=True)
