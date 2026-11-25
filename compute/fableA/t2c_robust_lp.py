r"""FABLE_A T2c [computed float]: robust mixed designs.  Fano classes 0..6; the three lines through class 0 are 'f'
(fully requested, chosen last, they absorb every damaged point); the four other lines (a quadrangle) are coloured a/b.
Typical sub-stratum j as in t2b: I = bottom of M, |I| = i = j*m/(m-t+j);
  'a' member = Y_a + I + W, W in M\I, |W| = t - i;   'b' member = S + Y_b, |S&Y_a| = j, |S&I| = i-j, |S&(M\I)| = t-i;
  'f' member >= S, |S| = t.   Slack s only in the three f rows (it has to exceed the damage O(sqrt k)/k, or 4*rho for many classes).
Prints max s over the 16 colourings of the quadrangle, for a grid of N and j in [0, om/3].  Usage: py t2c_robust_lp.py eps"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog
LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]

def solve(N, t, j, quad):
    om = N - 1 - t; m = N - 2*om; i = j*m/(m - t + j) if j > 0 else 0.0
    reg = [om, om, i, m - i]; nv = 29; idx = lambda c, r: 4*c + r
    A = []; b = []
    def row(L, regs, slack):
        v = np.zeros(nv)
        for c in L:
            for r in regs: v[idx(c, r)] = 1
        v[28] = slack; return v
    for L, ty in zip(LINES, "fff" + quad):
        if ty == 'a':
            A.append(row(L, [1], 0)); b.append(0.0); A.append(row(L, [3], 0)); b.append(t - i)
        elif ty == 'b':
            A.append(row(L, [0], 0)); b.append(j); A.append(row(L, [2], 0)); b.append(i - j); A.append(row(L, [3], 0)); b.append(t - i)
        else:
            A.append(row(L, [0,1,2,3], 1)); b.append(t)
    Aeq = np.zeros((4, nv))
    for r in range(4):
        for c in range(7): Aeq[r, idx(c, r)] = 1
    cost = np.zeros(nv); cost[28] = -1
    res = linprog(cost, A_ub=np.array(A), b_ub=np.array(b), A_eq=Aeq, b_eq=np.array(reg),
                  bounds=[(0, None)]*28 + [(None, None)], method="highs")
    return res.x[28] if res.status == 0 else None

if __name__ == "__main__":
    eps = float(sys.argv[1]); t = 0.75 + eps
    quads = ["".join(q) for q in itertools.product("ab", repeat=4) if 'a' in q and 'b' in q]
    worst = {}
    for N in np.arange(5*t - 2 + 0.005, 3 - t, 0.02):
        om = N - 1 - t; out = []
        for f in np.linspace(0, 1/3, 9):
            best = max(((solve(N, t, f*om, q) or -9), q) for q in quads)
            out.append(f"{best[0]:+.4f}{best[1]}")
        print(f"N={N:.3f} om={om:.3f} 2om-t={2*om-t:+.3f} | " + " ".join(out), flush=True)
