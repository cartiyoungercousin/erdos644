"""PETAL §28.3: integer version of the window-and-seal plan (all-singles adversary, s = 0) at small k.
Usage: py window_int.py k T d   (tau_X = tau_Y = (T+1)/2 rounded: tau_X + tau_Y = T + 1)"""
import sys, itertools
import numpy as np, highspy
sys.path.insert(0, __import__("os").path.dirname(__file__))
from window_lp import TYPES, PAIRS, ASSIGN

def plan(k, T, d, tX, tY, assign):
    n = tX - 1 + k - d
    wmax = min(tX - 1, T - tY)
    h = highspy.Highs(); h.setOptionValue("output_flag", False); INF = highspy.kHighsInf
    nv = [0]
    def var(lo=0, hi=INF, integ=True):
        h.addVar(lo, hi)
        if integ: h.changeColIntegrality(nv[0], highspy.HighsVarType.kInteger)
        nv[0] += 1; return nv[0] - 1
    def row(c, lo, hi):
        h.addRow(lo, hi, len(c), np.array(list(c.keys()), dtype=np.int32), np.array(list(c.values()), dtype=float))
    L = var(-INF, INF, False)
    mu = {M: var() for M in TYPES}
    row({mu[M]: 1 for M in TYPES}, n, n)
    for a in range(4): row({mu[M]: 1 for M in TYPES if a in M}, -INF, wmax)
    G = [var(tX) for _ in range(3)]
    for j in range(3):
        c = {mu[frozenset([a])]: 1 for a in range(4) if assign[a] == j}; c[G[j]] = -1
        row(c, -INF, -j * d)
    load = [dict() for _ in range(3)]; const = [0, 0, 0]
    for a in range(4):
        if assign[a] == 'D':
            xs = {P: var() for P in PAIRS}
            row({v: 1 for v in xs.values()}, d, d)
            for P, v in xs.items():
                for j in P: load[j][v] = 1
        else: const[assign[a]] += d
    for j in range(3):
        c = dict(load[j]); c[G[j]] = 1; c[L] = -1
        row(c, -INF, -const[j])
    h.changeColCost(L, 1.0); h.run()
    return h.getInfo().objective_function_value

if __name__ == "__main__":
    k, T, d = map(int, sys.argv[1:4])
    best = None
    for tX in sorted({(T + 1) // 2, T + 1 - (T + 1) // 2}):  # the family: tau_A = floor((T+1)/2), tau_F = the rest; X is either class
        tY = T + 1 - tX
        for A in ASSIGN:
            v = plan(k, T, d, tX, tY, A)
            if best is None or v < best[0]: best = (v, tX, tY, A)
    print("k=%d T=%d d=%d: least max centre request (all-singles leaks) = %g with tau_X=%d tau_Y=%d assignment %s  (T = %d)" % (k, T, d, best[0], best[1], best[2], best[3], T))
