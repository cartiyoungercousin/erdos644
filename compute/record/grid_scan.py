"""Float grid scan of the depth-1 sparsest-anchor game, class 'all' (wrapper around compute/r1b).
usage: py grid_scan.py T POT [--pden 20] [--dden 40] [--nproc 20]
POT: "c" (potential c*s1 + s2) or "a,b,g".  Writes out/scan_T_POT_pden_dden.jsonl with the
winning request D and pattern pool of every adaptive win (float; evidence only)."""
import os, sys, json, time, argparse
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "r1b")); sys.path.insert(0, os.path.join(HERE, "..", "r1"))
from fractions import Fraction
from multiprocessing import Pool


def work(job):
    tstr, pot, pden, dden, q = job
    import game, outer, game2
    t = float(Fraction(tstr)); x, y, z = (a / pden for a in q)
    s = sorted(q, reverse=True)
    vnum = pot[0] * s[0] + pot[1] * s[1] + pot[2] * s[2]
    t0 = time.time()
    if pot[2] == 0 and pot[0] >= pot[1] > 0 and (q[0] + 2 * q[1]) / pden > 2 - t + 1e-9 and 2 * q[0] <= pden:
        return dict(p=list(q), win="lemmaA", sec=0)
    rules = game.Rules(3 - 2 * t, pot=tuple(-v for v in pot), pot0=-vnum / pden, half=False)
    try:
        rr = outer.solve_profile(x, y, z, t, rules, den=dden, max_outer=1500)
    except Exception as e:
        return dict(p=list(q), win="error", err=repr(e))
    out = dict(p=list(q), win=rr["win"], sec=round(time.time() - t0, 1), phi=rr.get("phi"))
    if rr["win"] == "adaptive":
        out["D"] = rr["D"]; out["pool"] = [list(a) for a in rr["pool"]]
    return out


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("t"); ap.add_argument("pot")
    ap.add_argument("--pden", type=int, default=20); ap.add_argument("--dden", type=int, default=40)
    ap.add_argument("--nproc", type=int, default=20); ap.add_argument("--list", default=None)
    a = ap.parse_args()
    pot = tuple(float(v) for v in a.pot.split(",")) if "," in a.pot else (float(a.pot), 1.0, 0.0)
    t = float(Fraction(a.t))
    def valid(q):
        i, j, l = q
        return i >= j >= l >= 0 and i >= 1 and i + j <= a.pden and (i + j + l) / a.pden <= 3 - 2 * t + 1e-9
    if a.list: qs = [tuple(int(v) for v in s.split(",")) for s in a.list.split(";")]
    else: qs = [(i, j, l) for i in range(1, a.pden + 1) for j in range(i + 1) for l in range(j + 1) if valid((i, j, l))]
    import tables
    for q in range(27): tables.fast_index("quad", (q // 9, q // 3 % 3, q % 3))
    for ab in [(), (0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]: tables.fast_index("triple", ab)
    tag = f"{a.t.replace('/', '_')}_{a.pot.replace(',', '_')}_{a.pden}_{a.dden}" + ("_list" if a.list else "")
    fn = os.path.join(HERE, "out", f"scan_{tag}.jsonl")
    cnt = {}; stuck = []; t0 = time.time()
    with Pool(a.nproc) as pool, open(fn, "w") as f:
        for r in pool.imap_unordered(work, [(a.t, pot, a.pden, a.dden, q) for q in qs], chunksize=1):
            f.write(json.dumps(r) + "\n"); f.flush()
            cnt[str(r["win"])] = cnt.get(str(r["win"]), 0) + 1
            if r["win"] not in ("static", "adaptive", "lemmaA"): stuck.append(tuple(r["p"]))
    print(f"t={a.t} pot={pot} grid 1/{a.pden} req 1/{a.dden}: {len(qs)} profiles {cnt} stuck {sorted(stuck)} {round(time.time()-t0)}s")
