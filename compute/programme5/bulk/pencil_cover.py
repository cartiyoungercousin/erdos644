"""Static three-anchor finish, n-independent, over ALL seven-types, as a covering MILP (units of k).
Pencil x_a,x_b,x_c (empty triple intersection). X_i = pairwise-only part opposite i (X_a = D_bc), mass x_i;
E_i = private part of anchor i, mass e_i = 1 - x_j - x_l. Candidate pairs (pairs meeting all three anchors):
X_i--X_j (i != j) and E_i--X_i. A good seven exists if 4 blocks L_1..L_4 of mass <= t cover every candidate pair
(B_g = a member avoiding L_g; V - L_g has >= n - T points). Equivalently co-types I_x = trace on {a,b,c} plus
{g : x in L_g}, all in one maximal intersecting family: this ranges over all 715 types. Each point picks a
pattern P (nonempty subset of the 4 blocks); patterns used on adjacent regions must intersect.
t*(x) = min t. Fano (Lemma P1): t = |U|/2 = (3 - sum x)/2.  Rounding to integers costs O(1) (<= 16 patterns per region).
usage: py -3.14 pencil_cover.py GRID  -> logs/pencil_cover_<GRID>.log  (grid over x_a <= x_b <= x_c)"""
import sys, os, itertools
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
HERE = os.path.dirname(os.path.abspath(__file__))
REG = ['Xa', 'Xb', 'Xc', 'Ea', 'Eb', 'Ec']
ADJ = {('Xa', 'Xb'), ('Xa', 'Xc'), ('Xb', 'Xc'), ('Ea', 'Xa'), ('Eb', 'Xb'), ('Ec', 'Xc')}
PAT = list(range(1, 16))

def tstar(x, ret=False):
    xa, xb, xc = x
    mass = dict(Xa=xa, Xb=xb, Xc=xc, Ea=1 - xb - xc, Eb=1 - xa - xc, Ec=1 - xa - xb)
    R = [r for r in REG if mass[r] > 1e-9]
    nm = len(R) * len(PAT)
    # vars: m[r,p] (nm), u[r,p] (nm, binary), t
    nv = 2 * nm + 1
    idx = {(r, p): i for i, (r, p) in enumerate(itertools.product(R, PAT))}
    c = np.zeros(nv); c[-1] = 1
    A, lo, hi = [], [], []
    for r in R:                                   # mass conservation
        row = np.zeros(nv)
        for p in PAT: row[idx[r, p]] = 1
        A.append(row); lo.append(mass[r]); hi.append(mass[r])
    for (r, p), i in idx.items():                 # m <= mass * u
        row = np.zeros(nv); row[i] = 1; row[nm + i] = -mass[r]; A.append(row); lo.append(-np.inf); hi.append(0)
    for (r1, r2) in ADJ:                          # disjoint patterns on adjacent regions not both used
        if r1 not in R or r2 not in R: continue
        for p in PAT:
            for q in PAT:
                if p & q: continue
                row = np.zeros(nv); row[nm + idx[r1, p]] = 1; row[nm + idx[r2, q]] = 1
                A.append(row); lo.append(-np.inf); hi.append(1)
    for g in range(4):                            # block loads
        row = np.zeros(nv)
        for (r, p), i in idx.items():
            if p >> g & 1: row[i] = 1
        row[-1] = -1; A.append(row); lo.append(-np.inf); hi.append(0)
    integ = np.zeros(nv); integ[nm:2 * nm] = 1
    b = Bounds(np.zeros(nv), np.concatenate([np.full(nm, np.inf), np.ones(nm), [np.inf]]))
    res = milp(c, constraints=LinearConstraint(np.array(A), lo, hi), integrality=integ, bounds=b,
               options=dict(time_limit=60))
    if ret:
        sol = {(r, format(p, '04b')[::-1]): round(res.x[i], 4) for (r, p), i in idx.items() if res.x[i] > 1e-7}
        return res.fun, sol
    return res.fun

if __name__ == '__main__':
    G = int(sys.argv[1])
    os.makedirs(os.path.join(HERE, 'logs'), exist_ok=True)
    out = open(os.path.join(HERE, 'logs', 'pencil_cover_%d.log' % G), 'w')
    worst = (0, None)
    for i in range(G + 1):
        for j in range(i, G + 1):
            for l in range(j, G + 1):
                x = (i / (2 * G), j / (2 * G), l / (2 * G))     # x_i in [0, 1/2]
                if x[1] + x[2] > 1 + 1e-12: continue
                v = tstar(x)
                fano = (3 - sum(x)) / 2
                print('x=(%.4f,%.4f,%.4f) t*=%.5f fano=%.5f' % (*x, v, fano), file=out, flush=True)
                if v > worst[0]: worst = (v, x)
    print('MAX over grid of t*:', worst, file=out)
    v, sol = tstar(worst[1], ret=True)
    print('witness LP at worst shape:', v, sol, file=out)
    out.close(); print(worst)
