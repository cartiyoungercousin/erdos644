"""Finer-grid probe of the sparsest-anchor game near the boundary x + 2y = 2 - t of Lemma A,
where a coarser grid can miss stuck profiles (at t = 0.84 the 1/50 grid finds one,
(0.40,0.38,0.24), that the 1/25 grid does not see).

usage: py boundary_check.py VARIANT T PDEN [NPROC=16] [width=0.03]
Profiles (i,j,l)/PDEN with x <= 1/2, S <= 3 - 2t and 2 - t - width <= x + 2y <= 2 - t; requests
on the grid 1/PDEN.  Output: out/boundary_VARIANT_T_PDEN.jsonl and a summary line.
"""
import sys, json, os, time
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction
from multiprocessing import Pool

def work(job):
    import outer, game
    variant, t, den, i, j, l = job
    x, y, z = i / den, j / den, l / den
    try:
        r = outer.solve_profile(x, y, z, t, game.make_rules(variant, t, x, y, z), den=den, max_outer=1500)
        out = dict(p=[i, j, l], win=r["win"], outer=r.get("outer"))
        if r["win"] == "adaptive": out.update(D=[round(float(v), 6) for v in r["D"]], pool=r["pool"])
        return out
    except Exception as e:
        return dict(p=[i, j, l], err=repr(e))

if __name__ == "__main__":
    variant, tstr, den = sys.argv[1], sys.argv[2], int(sys.argv[3])
    nproc = int(sys.argv[4]) if len(sys.argv) > 4 else 16
    width = float(sys.argv[5]) if len(sys.argv) > 5 else 0.03
    t = float(Fraction(tstr))
    import tables
    for q in range(27): tables.fast_index("quad", (q // 9, q // 3 % 3, q % 3))
    for ab in [(), (0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]: tables.fast_index("triple", ab)
    jobs = []
    for i in range(1, den // 2 + 1):
        for j in range(0, i + 1):
            for l in range(0, j + 1):
                x, y, z = i / den, j / den, l / den
                if x + y + z > 3 - 2 * t + 1e-9: continue
                if not (2 - t - width - 1e-9 <= x + 2 * y <= 2 - t + 1e-9): continue
                jobs.append((variant, t, den, i, j, l))
    fn = f"out/boundary_{variant.replace(':', '').replace(',', '.')}_{tstr.replace('/', '_')}_{den}.jsonl"
    cnt = {}; stuck = []; t0 = time.time()
    with Pool(nproc) as pool, open(fn, "w") as f:
        for r in pool.imap_unordered(work, jobs, chunksize=2):
            f.write(json.dumps(r) + "\n"); f.flush()
            k = "err" if "err" in r else str(r["win"]); cnt[k] = cnt.get(k, 0) + 1
            if k == "None": stuck.append(tuple(v / den for v in r["p"]))
    print(variant, tstr, f"grid 1/{den}, {len(jobs)} profiles with {2 - t - width:.3f} <= x+2y <= {2 - t:.3f}:", cnt,
          "stuck:", sorted(stuck), "time", round(time.time() - t0), flush=True)
