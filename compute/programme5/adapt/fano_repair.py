"""Reviewer's 'weighted Fano repair' (co-edge form) run against the two-cluster adversary of BEAT78 Theorem O.
V = R1 u R2 (|R_i| = s = ceil((2-c)k); glue ignored, it is o(k)), co-edge K = V - B (|K| = 2s - k), pool Y with
|Y| = |K| - T, X = V - Y, m = |X|.  Fano lines with point order 1..7; X split into 7 classes X_lam of near-equal size;
round i requests S_i = L_i u R_i, L_i = union of X_lam over lines through i, R_i = union over lines whose last point
is i of M_a cap M_b (M_j = Y - K_j = Y cap B_j).  Adversary: any cluster with |R_j - S_i| >= k, B maximising |B cap Y|
(then overlap with earlier omissions).  Reports |S_i| against T and Q = sum of the realised |M_a cap M_b| against
the first-order slack 7T - 3m.   usage: py -3.14 fano_repair.py k t c ymode   (ymode: R1 | R2 | split | x<frac>)"""
import sys, math, itertools
LINES = [(1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 5, 6)]

def run(k, t, c, ymode, order=(1, 2, 3, 4, 5, 6, 7)):
    T = math.floor(t * k); s = math.ceil((2 - c) * k)
    R = [list(range(s)), list(range(s, 2 * s))]; V = R[0] + R[1]
    ysz = 2 * s - k - T
    if ymode == 'R1': Y = set(R[0][:ysz])
    elif ymode == 'R2': Y = set(R[1][:ysz])
    elif ymode == 'split': Y = set(R[0][:ysz // 2] + R[1][:ysz - ysz // 2])
    else:
        f = float(ymode[1:]); a = int(round(f * ysz)); Y = set(R[0][:a] + R[1][:ysz - a])
    X = [v for v in V if v not in Y]; m = len(X)
    pos = {p: i for i, p in enumerate(order)}
    cls = {lam: set(X[j::7]) for j, lam in enumerate(LINES)}
    M = {}; log = []; Q = 0
    for i in order:
        L = set().union(*[cls[l] for l in LINES if i in l])
        Rr = set()
        for l in LINES:
            if i in l and max(l, key=lambda p: pos[p]) == i:
                a, b = [p for p in l if p != i]
                Rr |= M[a] & M[b]; Q += len(M[a] & M[b])
        S = L | Rr
        best = None
        for j in (0, 1):
            free = [v for v in R[j] if v not in S]
            if len(free) < k: continue
            prev = [M[p] for p in M]
            free.sort(key=lambda v: (-(v in Y), -sum(v in mm for mm in prev)))
            B = set(free[:k])
            key = len(B & Y)
            if best is None or key > best[0]: best = (key, j, B)
        if best is None: log.append((i, len(S), 'no answer')); break
        _, j, B = best
        M[i] = B & Y
        log.append((i, len(S), j, len(M[i])))
    return T, m, Q, 7 * T - 3 * m, log

if __name__ == '__main__':
    k, t, c, ym = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), sys.argv[4]
    T, m, Q, slack, log = run(k, t, c, ym)
    print('k=%d t=%.3f c=%.4f Y=%s: T=%d m=%d  Q=%d  slack 7T-3m=%d  max|S_i|=%d' % (k, t, c, ym, T, m, Q, slack,
          max(r[1] for r in log)))
    for r in log: print('  round %s: |S|=%s cluster/|M| %s' % (r[0], r[1], r[2:]))
