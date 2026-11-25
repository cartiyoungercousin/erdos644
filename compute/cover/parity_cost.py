r"""CORE 107: cost of the linear-code ("anti-Pasch") mechanism, in nats per k.  [computed float; identities proved by hand]
A family C_lin = {K in C(V,c) : 1_K in L} for a linear code L (over F_2 or F_3).  Sum identities (107.1):
  good seven (N<2):  K_1+...+K_7 = 1_V + u (mod 2), |u| <= 4 delta      -> killed if d(1_V, L) > 4 delta
  pencil (b):        K_1+K_2+K_3 = 1_V + u (mod 2), |u| <= 4 eps        -> killed if d(1_V, L) > 4 eps
  Q' (a):            2*1_V - sum K_i (mod 3) has weight <= B_Q = (9t+N-8)/2 -> killed if d_3(2*1_V, L) > B_Q
  triangle (c):      K_1+K_2+K_3 = 1_{singles} (mod 2), a CODEWORD of weight in [3-3t, t]  -> killed if L has no
                     codeword of weight in [3-3t, t]; random-like L needs R > N h(t/N) for that
A random-like code L of redundancy R nats has coset-leader weight w with ball(w) ~ e^{R k}; covering forces R <= gamma
(heuristic, 107.2).  'cost' = log ball volume:  F_2: N h(d/N);  F_3: N h(d/N) + d ln 2.  Columns are costs; compare with gamma.
Usage: py parity_cost.py
"""
import math
def h(x): return 0.0 if x <= 0 or x >= 1 else -x*math.log(x) - (1-x)*math.log(1-x)
for t in (0.7501, 0.76, 0.78):
    print(f"t={t}:  N      gamma   seven(2) pencil(2) Q'(3)    tri(2)   | Sigma-total  seven/gamma  rig.seven(4d ln2)")
    lo, hi = 5*t - 2, min(2.0, 3 - t)
    for i in range(1, 11):
        N = lo + (hi - lo)*i/10; c = N - 1; w = c - t; d = N - 1.75; e = t - 0.75
        g = (N - t)*h(w/(N - t))
        s7 = N*h(4*d/N); pe = N*h(4*e/N); BQ = max(0.0, (9*t + N - 8)/2); q3 = N*h(BQ/N) + BQ*math.log(2)
        tr = N*h(t/N)
        print(f"     {N:.4f} {g:.4f}  {s7:.4f}   {pe:.4f}   {q3:.4f}  {tr:.4f}  |  {pe+q3+tr:.4f}    {s7/g:6.2f}      {4*d*math.log(2):.4f}")
