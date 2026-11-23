"""Re-solve (with the complete pattern tables only) the stuck profiles of a grid file whose
certificate failed exact_check, and rewrite the file.
usage: py repair.py out/grid_....jsonl VARIANT T [--dden N]"""
import os, sys, json
os.environ["R1_FULL_TABLES"] = "1"
from fractions import Fraction as Fr
import exact_check, outer, game

args = sys.argv[1:]; dden = None
if "--dden" in args:
    k = args.index("--dden"); dden = int(args[k + 1]); del args[k:k + 2]
fn, variant, tstr = args[:3]
pden = int(fn.replace("\\", "/").split("_")[-2])
if dden is None: dden = 2 * pden if pden < 40 else pden
t = Fr(tstr); out = []; nfix = 0; nstuck = 0; nbad = 0
for line in open(fn):
    r = json.loads(line)
    if r.get("win") is None and "cuts" in r:
        nstuck += 1
        tot, unc, used = exact_check.verify_stuck(*r["p"], pden, t, variant, r["cuts"], dden=dden, verbose=False)
        if unc:
            i, j, l = r["p"]; x, y, z = i / pden, j / pden, l / pden
            rr = outer.solve_profile(x, y, z, float(t), game.make_rules(variant, float(t), x, y, z), den=dden)
            new = dict(p=r["p"], win=rr["win"], phi=r["phi"], outer=rr.get("outer"), repaired=True)
            if rr["win"] == "adaptive": new.update(D=[round(float(v), 6) for v in rr["D"]], pool=rr["pool"])
            if "cuts" in rr:
                new["cuts"] = [([round(float(v), 6) for v in kv], [list(m) for m in los]) for kv, los in rr["cuts"]]
                tot, unc2, used = exact_check.verify_stuck(*r["p"], pden, t, variant, new["cuts"], dden=dden, verbose=False)
                nbad += unc2 > 0
            else: unc2 = None
            print(f"repaired {r['p']}: {unc} uncovered -> win={rr['win']} uncovered={unc2}", flush=True)
            r = new; nfix += 1
    out.append(r)
with open(fn, "w") as f:
    for r in out: f.write(json.dumps(r) + "\n")
print(f"{fn}: {nstuck} stuck records checked exactly, {nfix} re-solved, {nbad} still unverified")
