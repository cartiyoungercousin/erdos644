r"""CORE §84: tau* (exact, rational certificate) and tau (exact ILP) for edge families.
Families: (a) co-edge files fam_*.txt (edges = complements in [n]); (b) pool families (all k-subsets of k+T points);
(c) complete families on n points; (d) SAT 'rand' families of decide_family.build.
tau* is certified exactly: a rational primal cover y (every edge load >= 1) and a rational fractional matching w
(every point load <= 1) with equal totals.  Usage: py frac_gap.py"""
import itertools, sys, os, glob
from fractions import Fraction as Fr
import numpy as np, highspy
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "core9"))

def lp(edges, n, integer=False):
    h = highspy.Highs(); h.setOptionValue("output_flag", False)
    for _ in range(n): h.addVar(0, 1 if integer else highspy.kHighsInf)
    h.changeColsCost(n, np.arange(n, dtype=np.int32), np.ones(n))
    if integer:
        h.changeColsIntegrality(n, np.arange(n, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * n))
    for e in edges:
        idx = np.array(sorted(e), dtype=np.int32); h.addRow(1, highspy.kHighsInf, len(idx), idx, np.ones(len(idx)))
    h.run(); sol = h.getSolution()
    return h.getInfo().objective_function_value, list(sol.col_value), list(sol.row_dual)

def tau_star_exact(edges, n):
    val, y, w = lp(edges, n)
    for D in (1, 2, 3, 4, 6, 8, 12, 24, 120, 840, 10**4, 10**6):
        Y = [Fr(v).limit_denominator(D) for v in y]; W = [max(Fr(0), Fr(v).limit_denominator(D)) for v in w]
        if any(sum(Y[x] for x in e) < 1 for e in edges): continue
        load = [Fr(0)] * n
        for e, we in zip(edges, W):
            for x in e: load[x] += we
        if max(load) > 1: continue
        if sum(Y) == sum(W): return sum(Y), "exact"
    return Fr(val).limit_denominator(10**6), "float"

def report(name, edges, n, k, T):
    ts, tag = tau_star_exact(edges, n)
    tau = round(lp(edges, n, integer=True)[0])
    print(f"{name:34s} k={k:2d} T={T:2d} n={n:2d} |H|={len(edges):5d}  tau*={str(ts):>6s} ({float(ts):.4f}, {tag})"
          f"  tau={tau} [ILP exact]  tau/tau*={tau/float(ts):.3f}  (tau-1)/k={(tau-1)/k:.3f}  n/k={n/k:.3f}", flush=True)

def comp(n, K): full = set(range(n)); return [frozenset(full - K) for K in K]

if __name__ == "__main__":
    base = os.path.join(os.path.dirname(__file__), "..", "core9", "logs")
    for f in sorted(glob.glob(os.path.join(base, "fam_*.txt"))):
        _, k, T, n, _ = os.path.basename(f).split("_"); k, T, n = int(k), int(T), int(n)
        K = [frozenset(map(int, l.split())) for l in open(f) if l.strip()]
        report(os.path.basename(f), comp(n, K), n, k, T)
    for k, T in [(4, 3), (6, 5), (8, 6), (8, 7), (10, 8)]:
        m = k + T; n = m + (k + T) // 4
        report(f"pool |Y|={n-m}", [frozenset(e) for e in itertools.combinations(range(m), k)], n, k, T)
    for k, n in [(4, 6), (8, 13), (12, 20)]:
        report("complete", [frozenset(e) for e in itertools.combinations(range(n), k)], n, k, n - k)
    try:
        from decide_family import build
        for seed in (1, 2):
            fam, _, _ = build(8, 6, 15, 2, "rand", seed)
            K = [frozenset(x for x in range(15) if (m >> x) & 1) for m in fam]
            report(f"SAT rand R=2 seed={seed} (8,6,15)", comp(15, K), 15, 8, 6)
    except Exception as ex:
        print("SAT families skipped:", repr(ex))
