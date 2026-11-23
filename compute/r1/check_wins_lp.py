"""Second sanity check of requester wins, for rule variants whose admissible set is thin (so that
random sampling as in check_wins.py is hopeless): for every 'adaptive' record, maximize random
linear objectives over the admissible responses (MILP, no pool) and verify that each extreme
response found is closed by some pattern of the recorded pool.  Records with an empty pool claim
that NO admissible response exists; for them we just re-run the feasibility MILP.

usage: py check_wins_lp.py out/grid_....jsonl VARIANT T [nobj=60] [dden]
"""
import sys, json
from fractions import Fraction
import numpy as np
import game

def main(fn, variant, tstr, nobj=60, dden=None):
    t = float(Fraction(tstr)); pden = int(fn.replace("\\", "/").split("_")[-2])
    if dden is None: dden = 2 * pden if pden < 40 else pden
    rng = np.random.default_rng(1); n = nemp = bad = tested = 0; worst = -9.0
    for line in open(fn):
        r = json.loads(line)
        if r.get("win") != "adaptive": continue
        n += 1
        i, j, l = r["p"]; x, y, z = i / pden, j / pden, l / pden
        mass = game.cell_mass(x, y, z); rules = game.make_rules(variant, t, x, y, z)
        # the file stores D rounded to 6 decimals; snap it back to the request grid (otherwise a
        # sealed cell of size i/21 etc. would no longer be exactly sealed)
        d = [min(round(v * dden) / dden, m) if abs(round(v * dden) / dden - v) < 2e-6 else v for v, m in zip(r["D"], mass)]
        if not r["pool"]:
            nemp += 1
            kv, mu = game.adversary(mass, d, t, rules, [])
            if kv is not None: bad += 1; print("  NOT infeasible:", r["p"], kv)
            continue
        cls = {C.name: C for C in game.closures(mass, d)}
        rows = [cls[name].W[idx] @ cls[name].M for name, idx in r["pool"]]
        for _ in range(nobj):
            kv, _ = game.adversary(mass, d, t, rules, [], objective=rng.normal(size=7))
            if kv is None: break
            rm = np.array(game.region_mass(mass, kv))
            v = min(float((R @ rm).max()) for R in rows)
            tested += 1; worst = max(worst, v - t)
            if v > t + 1e-6: bad += 1; print("  NOT closed:", r["p"], [round(a, 4) for a in kv], v)
    print(f"{fn}: {n} adaptive wins ({nemp} with empty pool = no admissible response, re-checked); "
          f"{tested} extreme responses tested against the pools; failures: {bad}; max (load - t): {worst:+.2e}")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 60,
         int(sys.argv[5]) if len(sys.argv) > 5 else None)
