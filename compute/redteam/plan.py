"""Transfer her winning PLAN (which types are requested completely at each round) from a logged line to another
adversary of the mix.py family, re-optimise the remaining freedom (MILP, discard fixed), verify exactly at T.
Usage: py plan.py reffile alphas order tl [N]"""
import sys, json, mix, exact, show
d = json.loads(open(sys.argv[1]).readline())
al = [float(x) for x in sys.argv[2].split(",")]; al = al * 6 if len(al) == 1 else al
order = sys.argv[3]; tl = float(sys.argv[4]); N = float(sys.argv[5]) if len(sys.argv) > 5 else 2.0
# reference plan: replay the reference line in floats and record fully requested types per round
E = 7; m = {0: d["Ns"][0] - 1.0, 1: 1.0}; ref = []
for e in range(1, E):
    b = 1 << e; s = {int(J): v for J, v in d["sol"][e - 1].items()}; tot = sum(s.values()); lam = 1 / (d["Ns"][e] - tot)
    ref.append({J for J in m if m[J] > 2e-6 and m[J] - s.get(J, 0.0) < 2e-6})
    m2 = {}
    for J in m:
        a = m[J] - min(m[J], s.get(J, 0.0)); m2[J] = m[J] - lam * a
        if a > 2e-6: m2[J | b] = lam * a
    m = m2
st, zv, dr, bd, sol = mix.solve(0.759, [N] * 7, al, order, tl, d["drop"], ref=ref)
rec = dict(T=0.759, Ns=[N] * 7, alphas=al, order=order, drops=d["drop"], status=st, z=zv, bound=bd, drop=dr, sol=sol, plan_from=sys.argv[1])
if zv is not None and zv < -0.0015:
    try:
        ze, de, cov = exact.run(0.759, [N] * 7, sol, al, order, 0.001); rec["exact_z_float"] = float(ze); rec["exact_z_at_T"] = str(ze)
    except AssertionError as ex: rec["exact_error"] = str(ex)
print(json.dumps(rec), flush=True)
