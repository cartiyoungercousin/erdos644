"""depth-2 runs with an own output file. usage: py d2.py OUT NPROC DDEN "i,j,l;..." """
import sys, os, json
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"): os.environ.setdefault(_v, "1")
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "r1b")); sys.path.insert(0, os.path.join(here, "..", "r1"))
from multiprocessing import Pool
import multi
if __name__ == "__main__":
    qs = [tuple(int(v) for v in q.split(",")) for q in sys.argv[4].split(";")]
    jobs = [("0.84", "2000,40,1", 50, int(sys.argv[3]), q, 2, "all", False) for q in qs]
    with Pool(int(sys.argv[2])) as pool, open(os.path.join(here, sys.argv[1]), "a") as f:
        for r in pool.imap_unordered(multi.work, jobs, chunksize=1): f.write(json.dumps(r) + "\n"); f.flush()
