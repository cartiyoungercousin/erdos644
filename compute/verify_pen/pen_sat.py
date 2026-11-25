"""Independent SAT check of the pencil bound (A).  Written from the statement only.
Question: is there a k-uniform family H on [n] such that every (k+r)-subset contains a member,
and NO pencil (three DISTINCT members, empty common intersection) of weight |x1^x2^x3| <= P ?
UNSAT => the pencil bound holds at (n,k,r,P).  SAT => witness printed and re-verified by brute force.
Symmetry breaking: member {0..k-1} is forced (valid: H nonempty, relabel points).
usage: pen_sat.py n k r P [timeout_s]"""
import sys, threading, itertools, time
import numpy as np
from pysat.solvers import Solver
n, k, r, P = map(int, sys.argv[1:5]); TO = float(sys.argv[5]) if len(sys.argv) > 5 else 300
sets = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)]
idx = {m: i + 1 for i, m in enumerate(sets)}
M = np.array(sets, dtype=np.uint32); N = len(sets)
t0 = time.time()
import os
s = Solver(name=os.environ.get('PEN_SOLVER', 'cd15'))
cov = 0
for c in itertools.combinations(range(n), k + r):
    cm = sum(1 << i for i in c)
    s.add_clause([idx[sum(1 << i for i in sub)] for sub in itertools.combinations(c, k)]); cov += 1
s.add_clause([idx[(1 << k) - 1]])
pen = 0
ar = np.arange(N)
for i in range(N):
    a = M[i]
    B = M[i + 1:]
    if len(B) < 2: break
    ab = a & B; m = a ^ B
    ok = ((ab[:, None] & M[None, :]) == 0) & (np.bitwise_count(m[:, None] ^ M[None, :]) <= P) \
         & (ar[None, :] > (ar[i + 1:, None]))
    bi, ci = np.nonzero(ok)
    for b_, c_ in zip(bi.tolist(), ci.tolist()):
        s.add_clause([-(i + 1), -(i + 2 + b_), -(c_ + 1)]); pen += 1
gen = time.time() - t0
timer = threading.Timer(TO, s.interrupt); timer.start()
res = s.solve_limited(expect_interrupt=True); timer.cancel()
el = time.time() - t0
out = f"n={n} k={k} r={r} P={P}: vars={N} cover={cov} pencil_clauses={pen} -> "
if res is None: print(out + f"TIMEOUT ({el:.1f}s)"); sys.exit()
if res is False: print(out + f"UNSAT ({el:.1f}s)"); sys.exit()
model = s.get_model(); H = [sets[v - 1] for v in model if v > 0]
# brute-force re-verification of the witness
Hs = set(H)
covok = all(any((h & ~cm) == 0 for h in H) for cm in
            (sum(1 << i for i in c) for c in itertools.combinations(range(n), k + r)))
best = None
for x, y, z in itertools.combinations(H, 3):
    if x & y & z == 0:
        w = bin(x ^ y ^ z).count('1'); best = w if best is None else min(best, w)
print(out + f"SAT ({el:.1f}s) |H|={len(H)} covering={covok} min_pencil_weight={best}")
print("  witness:", [sorted(i for i in range(n) if h >> i & 1) for h in H][:60])
