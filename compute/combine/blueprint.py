"""Blueprint data: for every 1/25 anchor with s1 <= 0.56 at t = 0.84 (Phi = 2000 s1 + 40 s2 + s3, class all),
re-solve depth 1 without the top-level memo and record the winning line:
static, or adaptive with first request D (cells X,Y,Z,PE,PF,PG), sealed pair cells, closure types in the pool.
usage: py blueprint.py [nproc]  ->  blueprint_0.84.jsonl"""
import sys, os, json
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"): os.environ.setdefault(_v, "1")
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "r1b")); sys.path.insert(0, os.path.join(here, "..", "r1"))
from multiprocessing import Pool

def work(q):
    import multi, game
    multi.memo_get = lambda k: None; multi.memo_put = lambda k, v: None
    ctx = multi.Ctx("0.84", "2000,40,1", 25, 50, cls="all"); ctx.record = {}
    res = ctx.wins(q, ctx.phi(q), 1)
    rr = next(iter(ctx.record.values()), None)
    out = dict(p=list(q), win=bool(res), kind=None)
    if rr is not None:
        out["kind"] = rr["win"]
        if rr["win"] == "adaptive":
            mass = game.cell_mass(*(v / 25 for v in q)); d = rr["D"]
            out["D"] = [round(float(v), 4) for v in d]
            out["sealed"] = [c for c in range(3) if mass[c] > 1e-9 and d[c] >= mass[c] - 1e-9]
            out["closures"] = sorted({str(n) for n, i in rr["pool"]}); out["npool"] = len(rr["pool"])
    elif res: out["kind"] = "shortcut"
    return out

if __name__ == "__main__":
    qs = [(i, j, l) for i in range(1, 15) for j in range(i + 1) for l in range(j + 1) if i + j <= 25 and i + j + l <= 33]
    with Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 6) as pool, open(os.path.join(here, "blueprint_0.84.jsonl"), "w") as f:
        for r in pool.imap_unordered(work, qs, chunksize=4): f.write(json.dumps(r) + "\n"); f.flush()
    print("done", len(qs))
