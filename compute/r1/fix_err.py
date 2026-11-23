"""Re-solve the records of a grid file that ended with an error (rare solver failures) and
rewrite the file.   usage: py fix_err.py out/grid_....jsonl VARIANT T [--dden N]"""
import sys, json
from fractions import Fraction as Fr
import outer, game
args = sys.argv[1:]; dden = None
if "--dden" in args:
    k = args.index("--dden"); dden = int(args[k + 1]); del args[k:k + 2]
fn, variant, tstr = args[:3]
pden = int(fn.replace("\\", "/").split("_")[-2])
if dden is None: dden = 2 * pden if pden < 40 else pden
t = float(Fr(tstr)); out = []; n = 0
for line in open(fn):
    r = json.loads(line)
    if "err" in r:
        i, j, l = r["p"]; x, y, z = i / pden, j / pden, l / pden
        rr = outer.solve_profile(x, y, z, t, game.make_rules(variant, t, x, y, z), den=dden)
        r = dict(p=r["p"], win=rr["win"], phi=round(rr["phi"], 6), outer=rr.get("outer"), resolved=True)
        if rr["win"] == "adaptive": r.update(D=[round(float(v), 6) for v in rr["D"]], pool=rr["pool"])
        if "cuts" in rr: r["cuts"] = [([round(float(v), 6) for v in kv], [list(m) for m in los]) for kv, los in rr["cuts"]]
        print("re-solved", r["p"], "->", r["win"], flush=True); n += 1
    out.append(r)
with open(fn, "w") as f:
    for r in out: f.write(json.dumps(r) + "\n")
print(fn, "re-solved", n)
