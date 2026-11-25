r"""PETAL §41: SL1 test on unions of arena classes (continuous masses, exact LPs).
Family F = U_i A(R_i, rho_i), A(R, rho) = all mass-1 sets with >= 1 - rho in R, the rest anywhere (unbounded pool).
Regions are unions of Venn atoms sigma (nonempty subsets of [m]); s_sigma = atom mass.
  overlap(i,j) = max(0, 2 - rho_i - rho_j - |R_i u R_j|)     (i = j allowed)
  tau = LP min sum r  s.t.  sum_{sigma ni i} r_sigma >= |R_i| - 1 + rho_i,  0 <= r <= s
  Phi = LP min z + (8/3) beta  s.t.  beta >= rho_i + |R_i \ A|, h = |A| - 1 + beta, z >= h, z >= 2h - 2(t - 1 + c)
SL1 fails for F iff Phi >= t while theta(t) < c < 1 - 5t/9 and tau >= t/2.
usage: py multiarena.py t m restarts seed"""
import sys, itertools
import numpy as np
from scipy.optimize import linprog, minimize

def atoms(m):
    return [S for k in range(1, m + 1) for S in itertools.combinations(range(m), k)]

def evaluate(s, rho, t, AT, m):
    R = np.array([[1.0 if i in S else 0.0 for S in AT] for i in range(m)])
    sz = R @ s
    if np.any(sz < 1 - rho - 1e-12): return None
    c = min(max(0.0, 2 - rho[i] - rho[j] - float(((R[i] + R[j]) > 0) @ s)) for i in range(m) for j in range(i, m))
    na = len(AT)
    lo = sz - 1 + rho
    res = linprog(np.ones(na), A_ub=-R, b_ub=-lo, bounds=[(0, x) for x in s], method='highs')
    if res.status != 0: return None
    tau = res.fun
    # vars: x (na), beta, z
    cvec = np.r_[np.zeros(na), 8 / 3, 1.0]
    Aub = []; bub = []
    for i in range(m):   # rho_i + sum_{sigma in R_i}(s - x) <= beta
        Aub.append(np.r_[-R[i], -1.0, 0.0]); bub.append(-rho[i] - R[i] @ s)
    # h = sum x - 1 + beta <= z ; 2h - 2(t-1+c) <= z
    Aub.append(np.r_[np.ones(na), 1.0, -1.0]); bub.append(1.0)
    Aub.append(np.r_[2 * np.ones(na), 2.0, -1.0]); bub.append(2.0 + 2 * (t - 1 + c))
    r2 = linprog(cvec, A_ub=np.array(Aub), b_ub=np.array(bub), bounds=[(0, x) for x in s] + [(0, None), (None, None)], method='highs')
    if r2.status != 0: return None
    return dict(c=c, tau=tau, phi=r2.fun, d=1 - c - tau, x=r2.x[:na], beta=r2.x[na])

def objective(v, t, AT, m, theta, cmax):
    na = len(AT); s = np.abs(v[:na]); rho = np.clip(np.abs(v[na:]), 0, 1)
    e = evaluate(s, rho, t, AT, m)
    if e is None: return 10.0
    if e['c'] < theta - 0.25 or e['tau'] > 1: return 10.0
    pen = 0.0
    pen += 50 * max(0, theta + 1e-4 - e['c']) + 50 * max(0, e['c'] - cmax + 1e-4) + 50 * max(0, t / 2 - e['tau'])
    return -(min(e['phi'], t + 1) - t) + pen

if __name__ == '__main__':
    t = float(sys.argv[1]); m = int(sys.argv[2]); N = int(sys.argv[3]); seed = int(sys.argv[4])
    theta = (6 * t - 2) / 5; cmax = 1 - 5 * t / 9
    AT = atoms(m); rng = np.random.default_rng(seed); best = None
    for it in range(N):
        core = rng.uniform(0.6, 1.2); v0 = np.r_[[core if len(S) == m else rng.exponential(0.4 / m) * (rng.random() < 0.7) for S in AT], rng.random(m) * 0.2]
        r = minimize(objective, v0, args=(t, AT, m, theta, cmax), method='Nelder-Mead',
                     options=dict(maxiter=4000, xatol=1e-7, fatol=1e-9))
        if best is None or r.fun < best[0]:
            best = (r.fun, r.x)
            na = len(AT); s = np.abs(r.x[:na]); rho = np.clip(np.abs(r.x[na:]), 0, 1)
            e = evaluate(s, rho, t, AT, m)
            if e is not None:
                print(it, 'obj %.5f' % r.fun, 'c %.4f tau %.4f d %.4f phi %.4f beta %.4f' % (e['c'], e['tau'], e['d'], e['phi'], e['beta']),
                      's', np.round(s, 4).tolist(), 'rho', np.round(rho, 4).tolist(), flush=True)
    print('BEST objective (= t - phi + penalties) %.6f' % best[0])
