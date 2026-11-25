"""Exact ILP check (covering seven T-sets of an N-set, N=k+T, Z=empty, omega=0) at 4T=3k+1.
Expect INFEASIBLE for every k = 1 mod 4 (hand proof: parity, FINITE_K.md 1.3), and FEASIBLE for 4T=3k+3 controls."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'verify'))
from cover7_ilp import feasible
for k in [5, 9, 13, 17, 21]:
    T = (3*k+1)//4; N = k+T
    print("4T=3k+1 ", (k, T, N), feasible(N, N-k), flush=True)
for k in [3, 7, 11, 15]:
    T = (3*k+3)//4; N = k+T
    print("4T=3k+3 ", (k, T, N), feasible(N, N-k), flush=True)
