"""COMBINE 2: near-lex anchor (minimiser of 2000*s1 + 40*s2 + s3, class all), anchors with largest cell <= XMAX/pden.
usage: py run_lex.py T DEPTH PDEN DDEN XMAX [NPROC]"""
import sys, os, subprocess
from fractions import Fraction as Fr
t = Fr(sys.argv[1]); depth = sys.argv[2]; pden = int(sys.argv[3]); dden = sys.argv[4]; xmax = int(sys.argv[5])
nproc = sys.argv[6] if len(sys.argv) > 6 else "18"
smax = int((3 - 2 * t) * pden)
qs = [(i, j, l) for i in range(1, xmax + 1) for j in range(i + 1) for l in range(j + 1) if i + j <= pden and i + j + l <= smax]
print(f"t={t} anchors with x <= {xmax}/{pden}: {len(qs)}", flush=True)
here = os.path.dirname(os.path.abspath(__file__))
subprocess.run(["py", "multi.py", sys.argv[1], "2000,40,1", depth, "--cls", "all", "--pden", str(pden), "--dden", dden,
                "--nproc", nproc, "--list", ";".join("%d,%d,%d" % q for q in qs)], cwd=os.path.join(here, "..", "r1b"))
