r"""FABLE_A T2b [computed float]: first-order feasibility of mixed two-pool Fano designs at the TYPICAL sub-stratum.
Two-class reversed rule. Stratum j: |S & Y_a| = j, S & Y_b = empty. I = bottom segment of M of mass i = j*m/(m-t+j)
(m = |M| = N - 2 om), so that a typical S of the stratum leaves exactly j of I unrequested:  |S & I| = i - j, |S & (M\I)| = t - i.
  'a' member = Y_a + I + (S & (M\I))      (dump = (Y_a\S) + (I\S), mass om)
  'b' member = S + Y_b                    (|S & Y_a| = j, |S & I| = i - j, |S & (M\I)| = t - i)
  'f' member = S only, |S| <= t
Regions 0 = Y_a, 1 = Y_b, 2 = I, 3 = M\I. Seven Fano classes; maximise common slack s in the first-order capacity rows.
Usage: py t2b_typical_lp.py eps"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog
LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]

def solve(N, t, j, types):
    om = N - 1 - t; m = N - 2*om; i = j*m/(m - t + j) if j > 0 else 0.0
    reg = [om, om, i, m - i]; nv = 29; idx = lambda c, r: 4*c + r
    A = []; b = []
    def row(L, regs, slack):
        v = np.zeros(nv)
        for c in L:
            for r in regs: v[idx(c, r)] = 1
        v[28] = slack; return v
    for L, ty in zip(LINES, types):
        if ty == 'a':
            A.append(row(L, [1], 0)); b.append(0.0)
            A.append(row(L, [3], 1)); b.append(t - i)
        elif ty == 'b':
            A.append(row(L, [0], 0)); b.append(j)
            A.append(row(L, [2], 0)); b.append(i - j)
            A.append(row(L, [3], 1)); b.append(t - i)
        else:
            A.append(row(L, [0,1,2,3], 1)); b.append(t)
    Aeq = np.zeros((4, nv))
    for r in range(4):
        for c in range(7): Aeq[r, idx(c, r)] = 1
    cost = np.zeros(nv); cost[28] = -1
    res = linprog(cost, A_ub=np.array(A), b_ub=np.array(b), A_eq=Aeq, b_eq=np.array(reg),
                  bounds=[(0, None)]*28 + [(None, None)], method="highs")
    return (res.x[28], res.x[:28]) if res.status == 0 else (None, None)

def best(N, t, j, tlist):
    bs = None; bt = None
    for types in tlist:
        s, _ = solve(N, t, j, types)
        if s is not None and (bs is None or s > bs + 1e-9): bs, bt = s, types
    return bs, bt

if __name__ == "__main__":
    eps = float(sys.argv[1]); t = 0.75 + eps
    full = [ty for ty in itertools.product("abf", repeat=7) if 'a' in ty and 'b' in ty]
    # pass 1 at one point to find the useful type patterns, then reuse the 40 best everywhere
    short = set()
    for Np, fp in [(1.80, 1/12), (1.80, 1/3), (2.0, 1/6), (2.2, 1/12), (2.2, 1/3)]:
        sc = []
        for ty in full:
            s, _ = solve(Np, t, fp*(Np - 1 - t), ty)
            sc.append((-(s if s is not None else -9), ty))
        sc.sort(); short |= set(ty for _, ty in sc[:25])
    short = sorted(short)
    for N in [5*t - 2 + 0.01, 1.84, 1.92, 2.0, 2.08, 2.16, 3 - t - 0.01]:
        om = N - 1 - t; out = []
        for f in [0, 1/12, 1/6, 1/4, 1/3]:
            s, ty = best(N, t, f*om, short if f > 0 else full)
            out.append(f"j={f:.3f}om: s={s:+.4f} {''.join(ty)}")
        print(f"N={N:.3f} om={om:.3f} | " + " | ".join(out), flush=True)
