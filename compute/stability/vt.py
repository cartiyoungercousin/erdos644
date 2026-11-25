r"""Vertex-type SAT encoding of 'some r members have complements covering all pairs'.  slot i selects member m (x[i][m]),
y[i][v] = v in complement of slot i's member; pair (u,v) needs a common slot.  Slots ordered by member index."""
import numpy as np, random
from pysat.solvers import Solver
def find_cover_vt(M, n, r, forced=None, solver='cadical153', want_model=True):
    M = np.asarray(M, dtype=np.int64); N = len(M); full = (1 << n) - 1
    comp = [int(full ^ m) for m in M]
    cnt = [0]
    def new(): cnt[0] += 1; return cnt[0]
    cl = []
    slots = r + (1 if forced is not None else 0)
    X = [[new() for _ in range(N)] for _ in range(r)]
    Y = [[new() for _ in range(n)] for _ in range(slots)]
    for i in range(r):
        cl.append(list(X[i]))
        for m in range(N):
            for v in range(n):
                cl.append([-X[i][m], Y[i][v] if (comp[m] >> v) & 1 else -Y[i][v]])
        # at most one: implied by y consistency except for duplicates of identical y-pattern; members are distinct masks so fine
    if forced is not None:
        fc = full ^ forced
        for v in range(n): cl.append([Y[r][v] if (fc >> v) & 1 else -Y[r][v]])
    # symmetry: member index strictly increasing along slots 0..r-1 via prefix vars
    P = [[new() for _ in range(N)] for _ in range(r)]
    for i in range(r):
        for m in range(N):
            # P[i][m] <-> P[i][m-1] or X[i][m]
            if m == 0: cl += [[-P[i][m], X[i][m]], [P[i][m], -X[i][m]]]
            else:
                cl += [[-P[i][m], P[i][m - 1], X[i][m]], [P[i][m], -P[i][m - 1]], [P[i][m], -X[i][m]]]
    for i in range(r - 1):
        for m in range(N):
            cl.append([-X[i + 1][m], P[i][m - 1]] if m > 0 else [-X[i + 1][m]])
    for u in range(n):
        for v in range(u + 1, n):
            zs = []
            for i in range(slots):
                z = new(); cl += [[-z, Y[i][u]], [-z, Y[i][v]]]; zs.append(z)
            cl.append(zs)
    with Solver(name=solver, bootstrap_with=cl) as s:
        if not s.solve(): return None
        mo = s.get_model()
    out = []
    for i in range(r):
        for m in range(N):
            if mo[X[i][m] - 1] > 0: out.append(m); break
    return out
