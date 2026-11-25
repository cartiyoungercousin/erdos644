# Zero/one/two-anchor static finishes over all 716 seven-types (k-uniform, units k = 1).
# A finish at (N,t): co-type masses m_F (F in maximal intersecting M), total N; anchor members exact (size 1,
# realised by members of H), every other member's region R_i = {x: i not in I_x} has mass >= N - t (covering).
# Two anchors: B1 any member, B2 inside a request S (|S| = N-t) with |S cap B1| = s; the adversary picks
# d = |B1 cap B2| in the window [max(0, s - w), s], w = N - t - 1. By convexity both window ends suffice.
import json, itertools, sys
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction as Fr
rows = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', '..', 'programme2', 'verify', 'out', 'maxint7_classes_lp.json')))
def parse(hx):
    v = int(hx, 16); return [g for g in range(128) if v >> g & 1]
classes = [(parse(r['mask']), Fr(r['lp'])) for r in rows if r['lp'] != 'None']
nin = lambda F, i: 0 if F >> i & 1 else 1

def one(M, a, N):
    nf = len(M)  # vars m (nf), t
    c = np.zeros(nf+1); c[-1] = 1
    A_eq = [list(np.ones(nf))+[0], [nin(F,a) for F in M]+[0]]; b_eq = [N, 1]
    A_ub = [[-nin(F,i) for F in M]+[-1] for i in range(7) if i != a]; b_ub = [-N]*6
    r = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=[(0,None)]*nf+[(0,1)], method='highs')
    return r.fun if r.status == 0 else None

def two(M, a, b, N, case):
    nf = len(M); nv = 2*nf + 2  # m1, m2, s, t
    S, Tt = 2*nf, 2*nf+1
    c = np.zeros(nv); c[Tt] = 1
    A_eq, b_eq, A_ub, b_ub = [], [], [], []
    for j in range(2):
        off = j*nf
        row = np.zeros(nv); row[off:off+nf] = 1; A_eq.append(row); b_eq.append(N)
        for x in (a, b):
            row = np.zeros(nv); row[off:off+nf] = [nin(F,x) for F in M]; A_eq.append(row); b_eq.append(1)
        for i in range(7):
            if i in (a, b): continue
            row = np.zeros(nv); row[off:off+nf] = [-nin(F,i) for F in M]; row[Tt] = -1; A_ub.append(row); b_ub.append(-N)
        dv = [nin(F,a)*nin(F,b) for F in M]
        row = np.zeros(nv); row[off:off+nf] = dv
        if j == 1:            # d = s
            row[S] = -1; A_eq.append(row); b_eq.append(0)
        elif case == 'A':     # d = s - (N - t - 1) >= 0
            row[S] = -1; row[Tt] = -1; A_eq.append(row); b_eq.append(1 - N)
            r2 = np.zeros(nv); r2[S] = -1; r2[Tt] = -1; A_ub.append(r2); b_ub.append(1 - N)
        else:                 # d = 0, s <= N - t - 1
            A_eq.append(row); b_eq.append(0)
            r2 = np.zeros(nv); r2[S] = 1; r2[Tt] = 1; A_ub.append(r2); b_ub.append(N - 1)
    # s in [1 - t, min(1, N - t)]
    r3 = np.zeros(nv); r3[S] = -1; r3[Tt] = -1; A_ub.append(r3); b_ub.append(-1)
    r4 = np.zeros(nv); r4[S] = 1; r4[Tt] = 1; A_ub.append(r4); b_ub.append(N)
    r = linprog(c, A_ub=np.array(A_ub), b_ub=b_ub, A_eq=np.array(A_eq), b_eq=b_eq,
                bounds=[(0,None)]*(2*nf)+[(0,1),(0,1)], method='highs')
    return r.fun if r.status == 0 else None

Ns = [Fr(11,6), Fr(15,8), Fr(19,10), Fr(2), Fr(21,10), Fr(9,4)]
for N in Ns:
    Nf = float(N)
    b0 = min((Nf*(1 - 1/float(lp)), str(lp)) for M, lp in classes if lp <= N)
    b1 = (9, None); b2 = (9, None)
    for M, lp in classes:
        if lp > N: continue
        for a in range(7):
            v = one(M, a, Nf)
            if v is not None and v < b1[0] - 1e-9: b1 = (v, str(lp))
        for a, b in itertools.combinations(range(7), 2):
            for case in 'AB':
                v = two(M, a, b, Nf, case)
                if v is not None and v < b2[0] - 1e-9: b2 = (v, str(lp))
    print(f'N={str(N):6s}={Nf:.4f}  0-anchor t>={b0[0]:.4f} [{b0[1]}]  1-anchor t>={b1[0]:.4f} [{b1[1]}]  '
          f'2-anchor t>={b2[0]:.4f} [{b2[1]}]  C1 (2N+1)/6={(2*Nf+1)/6:.4f}', flush=True)
