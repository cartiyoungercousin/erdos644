"""Run check.py's per-certificate verification on every leaf of a (possibly incomplete) cover,
in parallel, and report which octree region is still uncovered.  usage: py check_leaves.py DIR [nproc]"""
import sys, os, json
from fractions import Fraction as Fr
from multiprocessing import Pool
import check

def one(a):
    d, path, fn, root = a
    try:
        cert = check.load(os.path.join(d, fn))
        b = [tuple(x) for x in root]
        for ch in path:
            o = int(ch); b = [((lo + hi) / 2, hi) if o >> i & 1 else (lo, (lo + hi) / 2) for i, (lo, hi) in enumerate(b)]
        check.need([(Fr(x), Fr(y)) for x, y in cert["box"]] == b, "box mismatch")
        W = check.check_cert(cert)
        return path, cert["kind"], None, (W.Ycov, W.Ymot, W.k0)
    except check.Bad as e:
        return path, None, str(e), None

if __name__ == "__main__":
    d = sys.argv[1]; npr = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    idx = json.load(open(os.path.join(d, "index.json")))
    root = [(Fr(a), Fr(b)) for a, b in idx["root"]]
    jobs = [(d, p, fn, root) for p, fn in idx["leaves"].items()]
    kinds = {}; bad = []; R = [Fr(0)] * 3
    with Pool(npr) as pool:
        for p, k, err, r in pool.imap_unordered(one, jobs, chunksize=20):
            if err: bad.append((p, err)); continue
            kinds[k] = kinds.get(k, 0) + 1; R = [max(a, b) for a, b in zip(R, r)]
    leaves = set(j[1] for j in jobs if j[1] not in dict(bad))
    def missing(path):
        if path in leaves: return 0
        if len(path) >= 8: return 1
        return sum(missing(path + str(o)) for o in range(8))
    print(f"{d}: {sum(kinds.values())} leaf certificates OK {kinds}; {len(bad)} rejected {bad[:3]}; "
          f"Ycov={float(R[0]):.3f} Ymot={float(R[1]):.3f} k0={float(R[2]):.1f}")
    print("uncovered (counted in level-8 boxes, volume share):", missing(""), "of", 8 ** 8)
