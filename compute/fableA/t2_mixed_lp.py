r"""FABLE_A T2 [computed float]: first-order feasibility of mixed two-pool Fano designs at stratum j.
Two-class reversed rule; requests of the stratum: |S & Y_a| = j, S & Y_b = empty, S avoids A_j = bottom j of M.
  type 'a' member:  Y_a + A_j + (S & Mrest),  |S & Mrest| = t - j      (dump = (Y_a \ S) + A_j)
  type 'b' member:  S + Y_b, |S & Y_a| <= j, |S & M| <= t - j
  type 'f' member:  S only (any reply), |S| <= t
Regions: 0 = Y_a (om), 1 = Y_b (om), 2 = A_j (j), 3 = Mrest (N - 2 om - j).  Seven Fano classes, lines = triples.
Maximise the common slack s in every capacity constraint.  Usage: py t2_mixed_lp.py eps"""
import itertools, sys
import numpy as np
from scipy.optimize import linprog
LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]

def solve(N, t, j, types):
    om = N - 1 - t; reg = [om, om, j, N - 2*om - j]
    if reg[3] < 0: return None
    nv = 28 + 1; idx = lambda c, r: 4*c + r
    A = []; b = []
    for L, ty in zip(LINES, types):
        def row(regs):
            v = np.zeros(nv)
            for c in L:
                for r in regs: v[idx(c, r)] = 1
            v[28] = 1; return v
        if ty == 'a':
            A.append(row([1])); b.append(0.0)            # no Y_b on an a-line (slack makes this infeasible unless s<=0) -> handle as equality below
            A.append(row([3])); b.append(t - j)
        elif ty == 'b':
            A.append(row([0])); b.append(j)
            A.append(row([2, 3])); b.append(t - j)
        else:
            A.append(row([0,1,2,3])); b.append(t)
    A = np.array(A); b = np.array(b)
    # a-lines: Y_b part must be exactly 0 -> remove slack from those rows
    k = 0
    for L, ty in zip(LINES, types):
        if ty == 'a': A[k, 28] = 0; k += 2
        elif ty == 'b': A[k, 28] = 0; k += 2      # Y_a-part <= j is exact (padding), no slack needed
        else: k += 1
    Aeq = np.zeros((4, nv)); beq = np.array(reg)
    for r in range(4):
        for c in range(7): Aeq[r, idx(c, r)] = 1
    cost = np.zeros(nv); cost[28] = -1
    res = linprog(cost, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=beq, bounds=[(0, None)]*28 + [(None, None)], method="highs")
    return res.x[28] if res.status == 0 else None

def best(N, t, j):
    bs = None; bt = None
    for types in itertools.product("abf", repeat=7):
        if types.count('a') == 0 or types.count('b') == 0: continue
        s = solve(N, t, j, types)
        if s is not None and (bs is None or s > bs + 1e-9): bs, bt = s, types
    return bs, bt

if __name__ == "__main__":
    eps = float(sys.argv[1]); t = 0.75 + eps
    Ns = [1.80, 1.92, 2.04, 2.16, 2.24]
    for N in Ns:
        om = N - 1 - t; out = []
        for f in [0, 0.25, 0.5, 0.75, 1.0]:
            s, ty = best(N, t, f*om)
            out.append(f"j={f:.2f}om: s={s:+.4f} {''.join(ty)}")
        print(f"N={N:.2f} om={om:.3f} | " + " | ".join(out), flush=True)
