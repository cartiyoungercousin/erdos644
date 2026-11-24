"""COMBINE: min-S anchor game restricted to S <= sigma0(t) = (17 - 11 t)/7 (Theorem 11.1 closes the rest).
Runs compute/r1b/multi.py with potential s1+s2+s3 (class all) on the anchors of the region.
usage: py run.py T DEPTH PDEN DDEN [NPROC] [extra grid steps above sigma0, default 1]
"""
import sys, os, subprocess
from fractions import Fraction as Fr
t = Fr(sys.argv[1]); depth = sys.argv[2]; pden = int(sys.argv[3]); dden = sys.argv[4]
nproc = sys.argv[5] if len(sys.argv) > 5 else "20"; pad = int(sys.argv[6]) if len(sys.argv) > 6 else 1
sig = (17 - 11 * t) / 7
smax = min(int(sig * pden) + pad, int((3 - 2 * t) * pden))
qs = [(i, j, l) for i in range(1, pden + 1) for j in range(i + 1) for l in range(j + 1) if i + j <= pden and i + j + l <= smax]
print(f"t={t} sigma0={float(sig):.4f} anchors with S <= {smax}/{pden}: {len(qs)}", flush=True)
here = os.path.dirname(os.path.abspath(__file__))
subprocess.run(["py", "multi.py", sys.argv[1], "1,1,1", depth, "--cls", "all", "--pden", str(pden), "--dden", dden,
                "--nproc", nproc, "--list", ";".join("%d,%d,%d" % q for q in qs)], cwd=os.path.join(here, "..", "r1b"))
