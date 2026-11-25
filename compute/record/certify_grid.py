"""Task (i): exact certificates for every grid-profile win of a scan (degenerate boxes).
usage: py certify_grid.py SCANFILE T C PDEN [--nproc N] [--out DIR]
Each won grid profile p gets a certificate on the box {p} (static, a Lemma-A request, or the
scan's request D); the profile stuck in the scan is reported.  Check: py check.py DIR/*.json.gz
"""
import os, sys, json, gzip, time, argparse
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction as Fr
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)


def work(job):
    r, t, C, pden, out = job
    import certify, search, cover
    t = Fr(t); C = Fr(C)
    p = [Fr(v, pden) for v in r["p"]]; box = [(v, v) for v in p]
    t0 = time.time(); cands = []
    if r["win"] == "static": cands = ["static"]
    elif r["win"] == "lemmaA": cands = cover.lemmaA_plans(C, t)
    elif r["win"] == "adaptive":
        D = [Fr(v).limit_denominator(4 * pden) for v in r["D"]]
        cands = [certify.plan_from_point(p, D, C, t)]
    else:
        return r["p"], r["win"], "not won in scan", 0
    err = ""
    for pl in cands:
        try:
            cert = certify.certify_box(box, pl, t, C, max_nodes=20000)
            fn = os.path.join(out, "p_%d_%d_%d.json.gz" % tuple(r["p"]))
            with gzip.open(fn, "wt") as f: json.dump(cert, f)
            return r["p"], r["win"], "ok", time.time() - t0
        except search.Fail as e:
            err = str(e)[:80]
    return r["p"], r["win"], "FAIL " + err, time.time() - t0


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("scan"); ap.add_argument("t"); ap.add_argument("C"); ap.add_argument("pden", type=int)
    ap.add_argument("--nproc", type=int, default=8); ap.add_argument("--out", default=None)
    a = ap.parse_args()
    out = a.out or os.path.join(HERE, "grid_" + os.path.basename(a.scan).replace(".jsonl", ""))
    os.makedirs(out, exist_ok=True)
    recs = [json.loads(l) for l in open(a.scan)]
    cnt = {}
    with Pool(a.nproc) as pool:
        for p, win, res, sec in pool.imap_unordered(work, [(r, a.t, a.C, a.pden, out) for r in recs]):
            key = f"{win}:{res.split()[0]}"; cnt[key] = cnt.get(key, 0) + 1
            if res != "ok": print(p, win, res, flush=True)
    print(a.scan, "t", a.t, "C", a.C, cnt)
