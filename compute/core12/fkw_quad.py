r"""CORE 111 (a): Q' quadruples in the FKW parity family, by MILP over the 16 Venn regions x 2 (X / Y). [solver-only;
the hand proof in CORE 111 is the exact statement].  Minimises the worst Q' violation
  viol = max( 2σ - (3T - n),  2(pair-only mass of matching) + 2σ - 2T  for the three matchings )   (doubled, integer)
over all quadruples of members (sizes c, |K_i ∩ X| odd). Q' holds for some quadruple iff min viol <= 0.
Usage: py -3.14 fkw_quad.py m [noparity]"""
import sys, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
m = int(sys.argv[1]); par = len(sys.argv) < 3
n, k, T, xs = 7 * m + 1, 4 * m, 3 * m, 4 * m; c = n - k
R = range(16); pc = lambda r: bin(r).count('1')
nv = 32 + 4 + 1  # x_r, y_r, w_i, v
X = lambda r: r; Y = lambda r: 16 + r; W = lambda i: 32 + i; V = 36
rows, lo, hi = [], [], []
def add(co, l, h):
    a = np.zeros(nv)
    for j, v in co: a[j] += v
    rows.append(a); lo.append(l); hi.append(h)
add([(X(r), 1) for r in R], xs, xs); add([(Y(r), 1) for r in R], n - xs, n - xs)
for i in range(4):
    rs = [r for r in R if r >> i & 1]
    add([(X(r), 1) for r in rs] + [(Y(r), 1) for r in rs], c, c)
    if par: add([(X(r), 1) for r in rs] + [(W(i), -2)], 1, 1)
sig = [r for r in R if pc(r) <= 1]
both = lambda r: [(X(r), 1), (Y(r), 1)]
add(sum((both(r) for r in sig), []) * 2 + [(V, -1)], -np.inf, 3 * T - n)          # 2σ - (3T-n) <= v
for M in [(0b0011, 0b1100), (0b0101, 0b1010), (0b1001, 0b0110)]:
    add(sum((both(r) for r in M), []) * 2 + sum((both(r) for r in sig), []) * 2 + [(V, -1)], -np.inf, 2 * T)
cost = np.zeros(nv); cost[V] = 1
ub = np.array([xs] * 16 + [n - xs] * 16 + [n] * 4 + [10 * n], float); lb = np.zeros(nv); lb[V] = -10 * n
res = milp(c=cost, constraints=LinearConstraint(np.array(rows), lo, hi), integrality=np.ones(nv), bounds=Bounds(lb, ub))
x = np.round(res.x).astype(int)
nr = [x[X(r)] + x[Y(r)] for r in R]
print(f"m={m} parity={par}: min doubled Q' violation = {round(res.fun)}  (Q' present iff <= 0); witness regions:",
      {format(r, '04b'): nr[r] for r in R if nr[r]})
