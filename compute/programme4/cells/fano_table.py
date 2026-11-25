"""Table of the Fano-sufficiency test from certs/fano_k*_T*_q*.jsonl (two cells; one cell rows separate)."""
import glob, json, re
from fractions import Fraction as F
rows = []
for fn in glob.glob('certs/fano_k*_T*_q*.jsonl'):
    k, T, q = map(int, re.findall(r'fano_k(\d+)_T(\d+)_q(\d+)', fn)[0])
    rs = [json.loads(l) for l in open(fn)]
    hi = [r for r in rs if 6 * r['n'] >= 11 * k]
    ex = sum(r['examined'] for r in hi); nf = [(e['tau'], r['a'], [j[0] for j in e['J']]) for r in rs for e in r['nonfano_only']]
    lo_nf = [x for r in rs if 6 * r['n'] < 11 * k for x in r['nonfano_only']]
    best = max(nf, key=lambda x: (x[0], -sum(x[1]))) if nf else None
    cl = (3 * k + 5) // 4
    rows.append((k, q, T, cl, ex, len(nf), len(lo_nf), sum(r['status'] == 'UNSAT' for r in rs), len(rs), best,
                 min((F(sum(x[1]), k) for x in nf), default=None)))
for r in sorted(rows):
    k, q, T, cl, ex, nf, lo, uns, tot, best, mn = r
    print(f"k={k:2d} q={q} T={T:2d} (tau>{T}, claimed {cl}): J examined at n>=11k/6: {ex:5d}  non-Fano-only: {nf:3d}"
          f"  (at n<11k/6: {lo})  UNSAT {uns}/{tot}  max-tau example: {best}  min n/k: {float(mn) if mn else '-'}")
