"""Grid evaluation of the one-round looseness-constrained game (outer.solve_profile per profile).

usage: py run_grid.py VARIANT T [--pden 20] [--dden 40] [--nproc 20] [--xmin 0] [--xmax 0.5] [--max-outer 3000]
  VARIANT: loose  -> S_max = 3 - 2t          (tight-triple lemma only)
           maxS   -> S_max = x + y + z       (anchor = good triple of maximum S in the family)
           none   -> no looseness inequality (baseline: one adaptive round, unconstrained adversary)
           minS   -> loose + every new good triple has S' >= x + y + z (anchor of minimum S)
           pot:a,b,c -> loose + Phi' <= Phi for every new good triple, Phi = a*s1 + b*s2 + c*s3 of the
                     sorted pair cells (anchor = good triple maximizing Phi); pot:1,1,1 = maxS
           M      -> loose + pair rule (x = largest pair intersection <= 1/2 in the family)
           MS     -> M + the anchor has maximum S among good triples through an M-pair
  T: budget, e.g. 0.85 or 5/6
Profiles: x >= y >= z >= 0 multiples of 1/pden, x + y <= 1, 0 < x <= xmax, x + y + z <= 3 - 2t.
Requests D: multiples of 1/dden (pden must divide dden) plus a remainder cell, see outer.py.
Output: out/grid_VARIANT_T_pden_xmax.jsonl, one JSON object per profile.
"""
import sys, json, os, time, argparse
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction
from multiprocessing import Pool

def work(job):
    import outer, game
    variant, t, pden, dden, i, j, l, mo = job
    x, y, z = i / pden, j / pden, l / pden
    t0 = time.time()
    try:
        r = outer.solve_profile(x, y, z, t, game.make_rules(variant, t, x, y, z), den=dden, max_outer=mo)
    except Exception as e:
        return dict(p=[i, j, l], err=repr(e))
    out = dict(p=[i, j, l], win=r["win"], phi=round(r["phi"], 6), sec=round(time.time() - t0, 1), outer=r.get("outer"))
    if r["win"] == "adaptive":
        out.update(D=[round(v, 6) for v in r["D"]], pool=r["pool"])
    if r["win"] in (None, "undecided") and "cuts" in r:
        out.update(cuts=[([round(v, 6) for v in kv], [list(m) for m in losing]) for kv, losing in r["cuts"]])
    return out

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("variant"); ap.add_argument("t")
    ap.add_argument("--pden", type=int, default=20); ap.add_argument("--dden", type=int, default=40)
    ap.add_argument("--nproc", type=int, default=20); ap.add_argument("--xmax", type=float, default=0.5)
    ap.add_argument("--max-outer", type=int, default=3000)
    ap.add_argument("--xmin", type=float, default=0.0)
    a = ap.parse_args()
    t = float(Fraction(a.t)); den = a.pden
    assert a.dden % den == 0
    import tables
    for q in range(27):
        tables.quad_table((q // 9, q // 3 % 3, q % 3)); tables.fast_index("quad", (q // 9, q // 3 % 3, q % 3))
    for ab in [(), (0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]:
        tables.triple_table(ab); tables.fast_index("triple", ab)
    jobs = []
    for i in range(1, den + 1):
        if i / den > a.xmax + 1e-9 or i / den < a.xmin - 1e-9: continue
        for j in range(0, min(i, den - i) + 1):
            for l in range(0, j + 1):
                if (i + j + l) / den <= 3 - 2 * t + 1e-9:
                    jobs.append((a.variant, t, den, a.dden, i, j, l, a.max_outer))
    jobs.sort(key=lambda jb: -(jb[4] + jb[5] + jb[6]))
    os.makedirs("out", exist_ok=True)
    vname = a.variant.replace(":", "").replace(",", ".")
    fn = f"out/grid_{vname}_{a.t.replace('/', '_')}{'x%g' % a.xmin if a.xmin else ''}_{den}_{a.xmax}.jsonl"
    t0 = time.time(); cnt = {}
    with Pool(a.nproc) as pool, open(fn, "w") as f:
        for res in pool.imap_unordered(work, jobs, chunksize=1):
            f.write(json.dumps(res) + "\n"); f.flush()
            key = "ERR" if "err" in res else str(res.get("win"))
            cnt[key] = cnt.get(key, 0) + 1
    print(a.variant, a.t, "profiles", len(jobs), cnt, "time", round(time.time() - t0), flush=True)
