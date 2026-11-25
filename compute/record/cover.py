"""Continuum cover of the anchor-profile region R by boxes, each with an exact certificate.

usage: py cover.py T C SCANFILE PDEN [--nproc 22] [--init 20] [--maxlevel 3] [--out DIR]
  SCANFILE: grid_scan.py output (float requests D at grid profiles, multiples of 1/PDEN).
Root box [0,1] x [0,1/2] x [0,1/2] (contains R); it is cut into an octree.  The first --init
levels are not certified (pure tiling) -- in practice --init gives the level whose boxes have
side 1/(2^level); a box is certified as
   outside  (box & R empty),  static (phi <= t on box & R),  or  plan (one request wins).
Plans are generated from the grid requests D0 at grid points near the box (affine tracking of
sealed / fully requested cells, budget correction on the partially requested cells) and from
Lemma-A requests.  Failed boxes are split (up to --maxlevel extra levels).
Output DIR/index.json + DIR/<path>.json.gz;  check with  py check.py DIR
"""
from __future__ import annotations
import os, sys, json, gzip, time, argparse, itertools
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
from fractions import Fraction as Fr
from multiprocessing import Pool
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

ROOT = [(Fr(0), Fr(1)), (Fr(0), Fr(1, 2)), (Fr(0), Fr(1, 2))]


def box_of(path):
    b = list(ROOT)
    for ch in path:
        o = int(ch); nb = []
        for i, (lo, hi) in enumerate(b):
            mid = (lo + hi) / 2
            nb.append((mid, hi) if o >> i & 1 else (lo, mid))
        b = nb
    return b


def size(c, p):
    x, y, z = p
    return [x, y, z, 1 - x - y, 1 - x - z, 1 - y - z][c]


SIZE_COEF = [((0, 0, 0), (1, 0, 0)), ((0, 0, 0), (0, 1, 0)), ((0, 0, 0), (0, 0, 1)),
             ((1,), (-1, -1, 0)), ((1,), (-1, 0, -1)), ((1,), (0, -1, -1))]


def size_aff(c):
    a = Fr(1) if c >= 3 else Fr(0)
    return a, [Fr(v) for v in SIZE_COEF[c][1]]


def plans_from_D0(p0, D0, C, t):
    """affine plans derived from a winning grid request D0 at p0."""
    import model
    mass0 = [size(c, p0) for c in range(6)]
    sealed = [c for c in range(3) if D0[c] == mass0[c]]
    full = [c for c in range(3, 6) if D0[c] == mass0[c] and mass0[c] > 0]
    part = [c for c in range(6) if c not in sealed and c not in full and 0 < D0[c]]
    zero = [c for c in range(6) if c not in sealed and c not in full and c not in part]
    out = []
    # delta(p) = t - sum_{sealed, full} |c|(p) - sum_part D0_c   (affine; 0 at p0 if sum D0 = t)
    def build(track, absorb, weights):
        da = t; db = [Fr(0)] * 3
        for c in track:
            a, b = size_aff(c); da -= a; db = [u - v for u, v in zip(db, b)]
        for c in range(6):
            if c not in track and c not in sealed and c in part: da -= D0[c]
        for c in sealed:
            a, b = size_aff(c); da -= a; db = [u - v for u, v in zip(db, b)]
        req = {}
        for c in range(6):
            if c in sealed: continue
            if c in track:
                a, b = size_aff(c); req[c] = (a, tuple(b))
            elif c in absorb:
                w = weights[c]
                req[c] = (D0[c] + w * da, tuple(w * v for v in db))
            elif D0[c] != 0:
                req[c] = (D0[c], (0, 0, 0))
        return model.Plan(sealed, req, C, t)
    tf = [c for c in full]
    if part:
        tot = sum(D0[c] for c in part)
        out.append(build(tf, part, {c: D0[c] / tot for c in part}))
        for c in part:
            out.append(build(tf, [c], {c: Fr(1)}))
    else:
        # nothing partial: let a full private absorb, or a zero cell take the slack
        for c in full:
            out.append(build([d for d in full if d != c], [c], {c: Fr(1)}) if True else None)
        for c in zero:
            out.append(build(tf, [c], {c: Fr(1)}))
    return out


def lemmaA_plans(C, t):
    """seal Y, request h = (t - y)/2 of E \\ Y = X u PE and h of G \\ Y = Z u PG (several splits)."""
    import model
    h = (t / 2, (Fr(0), Fr(-1, 2), Fr(0)))            # (t - y)/2
    def sub(f, g):
        return (f[0] - g[0], tuple(a - b for a, b in zip(f[1], g[1])))
    zero = (Fr(0), (Fr(0), Fr(0), Fr(0)))
    X = (Fr(0), (Fr(1), Fr(0), Fr(0))); Z = (Fr(0), (Fr(0), Fr(0), Fr(1)))
    PE = (Fr(1), (Fr(-1), Fr(-1), Fr(0))); PG = (Fr(1), (Fr(0), Fr(-1), Fr(-1)))
    splitsE = [(zero, h), (h, zero), (X, sub(h, X)), (sub(h, PE), PE)]
    splitsG = [(zero, h), (h, zero), (Z, sub(h, Z)), (sub(h, PG), PG)]
    out = []
    for (dX, dPE), (dZ, dPG) in itertools.product(splitsE, splitsG):
        req = {0: dX, 3: dPE, 2: dZ, 5: dPG}
        out.append(model.Plan([1], req, C, t))
    return out


def phi_float(p):
    import model
    o = model.static_option()
    U = np.zeros((1, 10)); U[0, :3] = [float(v) for v in p]
    return float(o.values(U).min())


def local_D(p, t, C, den):
    """float solve (compute/r1 engine, class all) at the rational profile p; returns D or None."""
    sys.path.insert(0, os.path.join(HERE, "..", "r1b")); sys.path.insert(0, os.path.join(HERE, "..", "r1"))
    import game, outer, game2
    x, y, z = (float(v) for v in p)
    vnum = float(C) * x + y
    rules = game.Rules(3 - 2 * float(t), pot=(-float(C), -1.0, 0.0), pot0=-vnum, half=False)
    try:
        rr = outer.solve_profile(x, y, z, float(t), rules, den=den, max_outer=1500)
    except Exception:
        return None
    if rr["win"] != "adaptive": return None
    return [Fr(v).limit_denominator(4 * den) for v in rr["D"]]


def try_box(job):
    path, cands, t, C, max_nodes, lden = job
    import model, search, certify
    t = Fr(t); C = Fr(C)
    box = box_of(path)
    t0 = time.time()
    log = []
    # outside?
    S = search.Searcher(t, [model.static_option()], max_nodes=10)
    prof = [(nm, c, r, False) for nm, c, r in model.profile_rows(t, box)]
    y = S.cert_empty(prof)
    if y is not None:
        return path, dict(kind="outside", box=[[str(a), str(b)] for a, b in box], t=str(t), C=str(C), E=y), log, time.time() - t0
    # static?
    corners = [tuple(c) for c in itertools.product(*box)]
    try:
        cert = certify.certify_box(box, "static", t, C, max_nodes=200)
        return path, cert, log + ["static"], time.time() - t0
    except search.Fail as e:
        log.append("static: " + str(e)[:60])
    for tag, pl in cands:
        try:
            cert = certify.certify_box(box, pl, t, C, max_nodes=max_nodes)
            cert["plan_src"] = tag
            return path, cert, log, time.time() - t0
        except search.Fail as e:
            log.append(f"{tag}: {str(e)[:70]}")
    if lden:
        # local float solve at the box centre rounded to the 1/lden grid
        ctr = [(lo + hi) / 2 for lo, hi in box]
        q = [Fr(max(1, round(v * lden)), lden) if box[i][1] > 0 else Fr(0) for i, v in enumerate(ctr)]
        q = sorted(q, reverse=True)
        D0 = local_D(q, t, C, lden)
        if D0 is not None and sum(D0) == t:
            for j, pl in enumerate(plans_from_D0(q, D0, C, t)):
                try:
                    cert = certify.certify_box(box, pl, t, C, max_nodes=max_nodes)
                    cert["plan_src"] = f"local{[str(v) for v in q]}#{j}"
                    return path, cert, log, time.time() - t0
                except search.Fail as e:
                    log.append(f"local#{j}: {str(e)[:70]}")
        else:
            log.append("local: no win at " + str([str(v) for v in q]))
    return path, None, log, time.time() - t0


class Scan:
    def __init__(self, fn, pden, t, C):
        self.pden = pden; self.rec = {}
        for line in open(fn):
            r = json.loads(line); self.rec[tuple(r["p"])] = r
        self.t, self.C = t, C

    def candidates(self, box, maxc=10):
        """plans from grid points within one grid step of the box, nearest to the centre first."""
        den = self.pden
        ctr = [(lo + hi) / 2 for lo, hi in box]
        rng = [range(int(np.floor(float(lo) * den)) - 1, int(np.ceil(float(hi) * den)) + 2) for lo, hi in box]
        pts = []
        for q in itertools.product(*rng):
            r = self.rec.get(q)
            if r is None: continue
            d2 = sum((Fr(a, den) - c) ** 2 for a, c in zip(q, ctr))
            pts.append((d2, q, r))
        pts.sort(key=lambda a: a[0])
        out = []; seen = set()
        lemA = any(r["win"] == "lemmaA" for _, _, r in pts)
        if lemA:
            for i, pl in enumerate(lemmaA_plans(self.C, self.t)):
                out.append((f"lemmaA{i}", pl))
        for d2, q, r in pts:
            if r["win"] != "adaptive": continue
            p0 = [Fr(a, den) for a in q]
            D0 = [Fr(v).limit_denominator(4 * den) for v in r["D"]]
            if sum(D0) != self.t: continue
            for j, pl in enumerate(plans_from_D0(p0, D0, self.C, self.t)):
                key = json.dumps(pl.to_json(), sort_keys=True)
                if key in seen: continue
                seen.add(key); out.append((f"D0{list(q)}#{j}", pl))
            if len(out) >= maxc + (16 if lemA else 0): break
        return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("t"); ap.add_argument("C"); ap.add_argument("scan"); ap.add_argument("pden", type=int)
    ap.add_argument("--nproc", type=int, default=22); ap.add_argument("--start", type=int, default=4)
    ap.add_argument("--maxlevel", type=int, default=7); ap.add_argument("--out", default=None)
    ap.add_argument("--max_nodes", type=int, default=3000); ap.add_argument("--maxc", type=int, default=10)
    ap.add_argument("--only", default=None, help="comma separated start paths")
    ap.add_argument("--lden", type=int, default=0, help="denominator of the local float solve (0 = off)")
    a = ap.parse_args()
    t = Fr(a.t); C = Fr(a.C)
    out = a.out or os.path.join(HERE, "certs_" + a.t.replace("/", "_") + "_C" + a.C)
    os.makedirs(out, exist_ok=True)
    scan = Scan(a.scan, a.pden, t, C)
    idxfn = os.path.join(out, "index.json")
    index = json.load(open(idxfn)) if os.path.exists(idxfn) else dict(t=str(t), C=str(C), root=[[str(x), str(y)] for x, y in ROOT], leaves={}, failed={})
    done = set(index["leaves"])
    if a.only: queue = a.only.split(",")
    else: queue = ["".join(p) for p in itertools.product("01234567", repeat=a.start)]
    # resume: drop paths already covered by a leaf at or above them
    def covered(p): return any(p[:i] in done for i in range(len(p) + 1))
    def expand(p):
        """resume: a start path with leaves strictly below it is split instead of redone."""
        if covered(p): return []
        if any(l.startswith(p) and l != p for l in done):
            return [q for o in range(8) for q in expand(p + str(o))]
        return [p]
    queue = [q for p in queue for q in expand(p)]
    # remove queue items whose descendants are leaves (partially done): expand them
    t0 = time.time(); nfail = 0
    with Pool(a.nproc) as pool:
        while queue:
            jobs = [(p, scan.candidates(box_of(p), a.maxc), a.t, a.C, a.max_nodes, a.lden) for p in queue]
            queue = []
            for path, cert, log, sec in pool.imap_unordered(try_box, jobs, chunksize=1):
                if cert is not None:
                    fn = path + ".json.gz" if path else "root.json.gz"
                    with gzip.open(os.path.join(out, fn), "wt") as f: json.dump(cert, f)
                    index["leaves"][path] = fn; index["failed"].pop(path, None)
                    kind = cert["kind"] + ("" if cert["kind"] != "plan" else ":" + cert.get("plan_src", ""))
                    print(f"[{time.time()-t0:7.0f}s] {path:10s} {kind:40s} {sec:6.1f}s", flush=True)
                else:
                    if len(path) - a.start >= a.maxlevel or len(path) >= a.start + a.maxlevel:
                        index["failed"][path] = log; nfail += 1
                        print(f"[{time.time()-t0:7.0f}s] {path:10s} FAILED (max level) {log[-3:]}", flush=True)
                    else:
                        queue += [path + str(o) for o in range(8)]
                        print(f"[{time.time()-t0:7.0f}s] {path:10s} split  {log[-2:]}", flush=True)
                with open(idxfn + ".tmp", "w") as f: json.dump(index, f)
                for _try in range(50):
                    try: os.replace(idxfn + ".tmp", idxfn); break
                    except PermissionError: time.sleep(0.2)
    print(f"done: {len(index['leaves'])} leaves, {len(index['failed'])} failed, {time.time()-t0:.0f}s")


if __name__ == "__main__":
    main()
