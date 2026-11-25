"""Sanity checks for qlib: complete families, FKW, exactness lemma (both Fano methods + general seven)."""
import time, sys, numpy as np
from qlib import *

def run(name, n, k, G, l, a, gen=True, colsat=False):
    t0 = time.time()
    qv = qtable(n, G, l); tau, M = tau_levelset(n, k, qv, a); rL = n - k - tau + 1
    f, fw, st = fano_exact(n, k, G, l, a, qv, rL)
    if fw: assert check_seven(fw, n) and all(bin(B).count('1') == k and qv[B] == a for B in fw)
    f2 = fano_sat(n, k, G, l, a, budget=2_000_000)[0] if colsat else '-'
    s, sw = seven_sat(n, k, G, l, a, budget=2_000_000) if gen else ('-', None)
    if sw: assert check_seven(sw, n) and all(bin(B).count('1') == k and qv[B] == a for B in sw)
    print(f"{name:30s} n={n} k={k} c={4*n-7*k:3d} |L|={M:7d} tau={tau:2d} rL={rL} fano={f:6s}({st[0]}dv,{st[1]}sat) colsat={f2:7s} any={s:7s} {time.time()-t0:.1f}s", flush=True)

for n in (13, 14):
    run(f"complete K({n})", n, 8, [0]*n, 0, 0, gen=False)
run("FKW m=2 (l=1_X,|X|=8)", 15, 8, [0]*15, (1 << 8) - 1, 1)
run("FKW m=3 (l=1_X,|X|=12)", 22, 12, [0]*22, (1 << 12) - 1, 1, gen=False)
# (random 4n = 7k instances: see exactness.py; the a = 1 UNSAT is a parity argument, slow for CDCL)
