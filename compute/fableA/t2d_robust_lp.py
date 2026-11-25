r"""FABLE_A T2d [computed float]: as t2c, but each b-line takes its request from its own stratum j_b in [0, j*]
(all strata below the switch j* are b-dominant), with the typical profile on (I, M\I):
  'a' member = Y_a + I + W, |W| = t - i, i = j* m/(m - t + j*)            (stratum j*, typical)
  'b' member = S + Y_b, |S&Y_a| = j_b, |S&I| = i (t - j_b)/m, |S&(M\I)| = (m - i)(t - j_b)/m
  'f' member >= S, |S| = t;  slack s in the three f rows only (f-lines = pencil through class 0).
Usage: py t2d_robust_lp.py eps"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog
LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]

def solve(N, t, j, quad):
    om = N - 1 - t; m = N - 2*om; i = j*m/(m - t + j) if j > 0 else 0.0
    reg = [om, om, i, m - i]; nv = 28 + 1 + 4; idx = lambda c, r: 4*c + r      # 28 masses, slack, j_b per quadrangle line
    A = []; b = []
    def row(L, regs, slack=0):
        v = np.zeros(nv)
        for c in L:
            for r in regs: v[idx(c, r)] = 1
        v[28] = slack; return v
    for n_, (L, ty) in enumerate(zip(LINES, "fff" + quad)):
        if ty == 'a':
            A.append(row(L, [1])); b.append(0.0); A.append(row(L, [3])); b.append(t - i)
        elif ty == 'b':
            jb = 29 + n_ - 3
            v = row(L, [0]); v[jb] = -1; A.append(v); b.append(0.0)                     # Y_a part <= j_b
            v = row(L, [2]); v[jb] = i/m; A.append(v); b.append(i*t/m)                   # I part <= i (t - j_b)/m
            v = row(L, [3]); v[jb] = (m - i)/m; A.append(v); b.append((m - i)*t/m)       # rest <= (m-i)(t-j_b)/m
        else:
            A.append(row(L, [0,1,2,3], 1)); b.append(t)
    Aeq = np.zeros((4, nv))
    for r in range(4):
        for c in range(7): Aeq[r, idx(c, r)] = 1
    cost = np.zeros(nv); cost[28] = -1
    res = linprog(cost, A_ub=np.array(A), b_ub=np.array(b), A_eq=Aeq, b_eq=np.array(reg),
                  bounds=[(0, None)]*28 + [(None, None)] + [(0, j)]*4, method="highs")
    return res.x[28] if res.status == 0 else None

if __name__ == "__main__":
    eps = float(sys.argv[1]); t = 0.75 + eps
    quads = ["".join(q) for q in itertools.product("ab", repeat=4) if 'a' in q and 'b' in q]
    for N in np.arange(5*t - 2 + 0.005, 3 - t, 0.02):
        om = N - 1 - t; out = []
        for f in np.linspace(0, 1/3, 9):
            best = max(((solve(N, t, f*om, q) if solve(N, t, f*om, q) is not None else -9), q) for q in quads)
            out.append(f"{best[0]:+.4f}{best[1]}")
        print(f"N={N:.3f} om={om:.3f} | " + " ".join(out), flush=True)
