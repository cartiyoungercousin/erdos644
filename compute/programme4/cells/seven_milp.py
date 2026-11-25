r"""Second solver for the seven question (HiGHS MILP, independent formulation of the same criterion):
binary y_S (127 co-types), y_S + y_T <= 1 for disjoint S, T; integer x[i][S] <= a_i y_S, sum_S x[i][S] = a_i;
binary z[m][t] (member m takes profile J[t]), sum_t z[m][t] = 1, and the MONOTONE form
sum_{S not containing m} x[i][S] >= sum_t J[t]_i z[m][t] for every cell i.
Feasible iff H_J has a good seven.  Used to double-check SEVEN_FREE verdicts (CP-SAT) of extremal families.
usage: seven_milp.py k a1,a2,.. 'j;j;..'   (j as comma tuples)"""
import sys
import numpy as np
import highspy

TYPES = list(range(1, 128))


def seven_milp(a, k, J, time_limit=3600, types=None):
    global TYPES
    TYPES = list(range(1, 128)) if types is None else list(types)
    q = len(a); nT = len(TYPES); nJ = len(J)
    h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('time_limit', float(time_limit))
    h.setOptionValue('threads', 1)
    inf = highspy.kHighsInf
    # variable layout: y (nT), x (q*nT), z (7*nJ)
    lo = [0] * nT + [0] * (q * nT) + [0] * (7 * nJ)
    up = [1] * nT + [a[i] for i in range(q) for _ in TYPES] + [1] * (7 * nJ)
    nv = len(lo)
    h.addVars(nv, np.array(lo, float), np.array(up, float))
    h.changeColsIntegrality(nv, np.arange(nv, dtype=np.int32), np.array([1] * nv, dtype=np.uint8))
    X = lambda i, s: nT + i * nT + s
    Z = lambda m, t: nT + q * nT + m * nJ + t

    def row(lb, ub, idx, val):
        h.addRow(lb, ub, len(idx), np.array(idx, dtype=np.int32), np.array(val, float))
    for s, S in enumerate(TYPES):
        for s2 in range(s + 1, nT):
            if S & TYPES[s2] == 0:
                row(-inf, 1, [s, s2], [1, 1])
        for i in range(q):
            row(-inf, 0, [X(i, s), s], [1, -a[i]])
    for i in range(q):
        row(a[i], a[i], [X(i, s) for s in range(nT)], [1] * nT)
    for m in range(7):
        row(1, 1, [Z(m, t) for t in range(nJ)], [1] * nJ)
        for i in range(q):
            idx = [X(i, s) for s, S in enumerate(TYPES) if not (S >> m) & 1] + [Z(m, t) for t in range(nJ)]
            val = [1] * (len(idx) - nJ) + [-J[t][i] for t in range(nJ)]
            row(0, inf, idx, val)
    h.run()
    st = h.modelStatusToString(h.getModelStatus())
    return st                      # 'Optimal' = seven exists, 'Infeasible' = seven-free


if __name__ == '__main__':
    k = int(sys.argv[1]); a = tuple(int(v) for v in sys.argv[2].split(','))
    J = [tuple(int(v) for v in j.split(',')) for j in sys.argv[3].split(';')]
    print(seven_milp(a, k, J))
