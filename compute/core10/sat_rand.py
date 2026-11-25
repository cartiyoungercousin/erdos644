import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "core9"))
from frac_gap import report, comp
from decide_family import build
for R, mode, seed in [(3, "rand", 1), (3, "rand", 2), (3, "rand", 3)]:
    try:
        fam, _, _ = build(8, 6, 15, R, mode, seed)
    except AssertionError:
        print(f"R={R} {mode} seed={seed}: SAT instance unsatisfiable (no pencil-free selection)"); continue
    K = [frozenset(x for x in range(15) if (m >> x) & 1) for m in fam]
    report(f"SAT {mode} R={R} seed={seed} (8,6,15)", comp(15, K), 15, 8, 6)
