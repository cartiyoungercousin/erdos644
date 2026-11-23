"""Scan of extremal anchor choices ("potentials").

The anchor is a good triple maximizing Phi = a*s1 + b*s2 + c*s3 (s1 >= s2 >= s3 its pair cells)
over all good triples of the family; then every response that creates a new good triple (i.e.
every response to a request sealing a pair cell) must have Phi' <= Phi.  (1,1,1) = maxS,
(-1,-1,-1) = minS.  Rules only restrict the adversary, so profiles that the requester wins with
no rule stay won; we re-solve only the profiles that are stuck for variant `none`.

usage: py potential_scan.py T [NPROC=18] [pden=20] [dden=40] [pot|poth] [small | list=a,b,c;d,e,f TAG]
  pot : the anchor is extremal among ALL good triples (then anchors with a pair cell > 1/2 must
        also be handled; they are not in the profile grid);
  poth: the anchor is extremal among good triples with all pair cells <= 1/2; a response creating
        a good triple with a pair cell > 1/2 is then not constrained (the honest version for the
        profile grid x <= 1/2).
output: out/{pot,poth}scan_T.jsonl  (one line per (potential, profile)), summary on stdout.
"""
import sys, json, os, itertools, time
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction
from multiprocessing import Pool

EXTRA = [(1, .3, .1), (-1, -.3, -.1), (1, .5, 0), (0, 1, .5), (2, 1, 1), (1, 1, 2), (-2, -1, -1), (-1, -1, -2),
         (1, 2, 1), (-1, -2, -1), (1, -.5, -.5), (-1, .5, .5), (2, -1, -1), (-2, 1, 1), (1, 1, -2), (-1, -1, 2)]

def work(job):
    import outer, game
    pot, t, pden, dden, p, kind = job
    x, y, z = (v / pden for v in p)
    variant = kind + ":%g,%g,%g" % pot
    try:
        r = outer.solve_profile(x, y, z, t, game.make_rules(variant, t, x, y, z), den=dden, max_outer=3000)
        out = dict(pot=pot, p=p, win=r["win"], outer=r.get("outer"))
        if "cuts" in r: out["cuts"] = [([round(float(v), 6) for v in kv], [list(m) for m in los]) for kv, los in r["cuts"]]
        if "D" in r: out["D"] = [round(float(v), 6) for v in r["D"]]; out["pool"] = r["pool"]
        return out
    except Exception as e:
        return dict(pot=pot, p=p, err=repr(e))

if __name__ == "__main__":
    tstr = sys.argv[1]; t = float(Fraction(tstr))
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 18
    pden = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    dden = int(sys.argv[4]) if len(sys.argv) > 4 else 40
    kind = sys.argv[5] if len(sys.argv) > 5 else "pot"       # "poth": anchors with all cells <= 1/2
    base = f"out/grid_none_{tstr.replace('/', '_')}_{pden}_0.5.jsonl"
    stuck = [json.loads(l)["p"] for l in open(base) if json.loads(l).get("win") is None]
    pots = [p for p in itertools.product((-1, 0, 1), repeat=3) if any(p)] + EXTRA
    if len(sys.argv) > 6 and sys.argv[6] == "small":
        pots = [(1, 1, 1), (-1, -1, -1), (1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (0, 0, -1),
                (1, 1, 0), (-1, -1, 0), (0, 1, 1), (0, -1, -1), (1, -1, 0), (-1, 1, 0), (1, 0, -1), (-1, 0, 1),
                (1, -1, -1), (-1, 1, 1)]
    import tables
    for q in range(27): tables.fast_index("quad", (q // 9, q // 3 % 3, q % 3))
    for ab in [(), (0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]: tables.fast_index("triple", ab)
    tag = ""
    if len(sys.argv) > 6 and sys.argv[6].startswith("list="):       # e.g. list=-2,-1,0;-3,-1,0
        pots = [tuple(float(v) for v in q.split(",")) for q in sys.argv[6][5:].split(";")]
        tag = "_" + (sys.argv[7] if len(sys.argv) > 7 else "custom")
    jobs = [(pot, t, pden, dden, p, kind) for pot in pots for p in stuck]
    res = {}
    fn = f"out/{kind}scan_{tstr.replace('/', '_')}{tag}.jsonl"
    with Pool(nproc) as pool, open(fn, "w") as f:
        for r in pool.imap_unordered(work, jobs, chunksize=1):
            f.write(json.dumps(r) + "\n"); f.flush()
            res.setdefault(tuple(r["pot"]), []).append(r)
    print(f"t = {tstr}: {len(stuck)} profiles stuck with no rule; per potential (a,b,c): number still stuck")
    for pot in sorted(res, key=lambda q: sum(1 for r in res[q] if r.get("win") is None or "err" in r)):
        rs = res[pot]
        st = sorted(tuple(r["p"]) for r in rs if "err" not in r and r["win"] is None)
        er = sum(1 for r in rs if "err" in r or r.get("win") == "undecided")
        print(f"  {str(pot):22s} stuck {len(st):2d}  err/undecided {er}   " + " ".join("(%g,%g,%g)" % tuple(v / pden for v in p) for p in st))
