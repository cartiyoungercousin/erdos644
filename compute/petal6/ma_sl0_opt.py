r"""PETAL §41.2: adversarial optimisation of the SL0 gap on unions of m arena classes.
gap = (min beta(A) s.t. h(A) <= tau) - d, maximised by Nelder-Mead over atom masses and leaks, subject to c >= c0
(and tau >= tau0).  usage: py ma_sl0_opt.py m c0 tau0 restarts seed"""
import sys, numpy as np
from scipy.optimize import linprog, minimize
from multiarena import atoms, evaluate

def sl0gap(s, rho, AT, m):
    e = evaluate(s, rho, 0.75, AT, m)
    if e is None: return None, None
    na = len(AT); R = np.array([[1.0 if i in S else 0.0 for S in AT] for i in range(m)])
    Aub = [np.r_[-R[i], -1.0] for i in range(m)]; bub = [-rho[i] - R[i] @ s for i in range(m)]
    Aub.append(np.r_[np.ones(na), 1.0]); bub.append(1 + e['tau'])
    r = linprog(np.r_[np.zeros(na), 1.0], A_ub=np.array(Aub), b_ub=np.array(bub), bounds=[(0, x) for x in s] + [(0, None)], method='highs')
    if r.status != 0: return None, e
    return r.fun - e['d'], e

if __name__ == '__main__':
    m = int(sys.argv[1]); c0 = float(sys.argv[2]); tau0 = float(sys.argv[3]); N = int(sys.argv[4]); rng = np.random.default_rng(int(sys.argv[5]))
    AT = atoms(m); na = len(AT); best = None
    def obj(v):
        s = np.abs(v[:na]); rho = np.clip(np.abs(v[na:]), 0, 1)
        g, e = sl0gap(s, rho, AT, m)
        if g is None or e['c'] < c0 - 0.2: return 5.0
        return -g + 30 * max(0, c0 - e['c']) + 30 * max(0, tau0 - e['tau'])
    for it in range(N):
        core = rng.uniform(0.5, 1.3)
        v0 = np.r_[[core if len(S) == m else rng.exponential(0.4 / m) * (rng.random() < 0.7) for S in AT], rng.random(m) * 0.25]
        r = minimize(obj, v0, method='Nelder-Mead', options=dict(maxiter=6000, xatol=1e-8, fatol=1e-10))
        if r.fun < 4 and (best is None or r.fun < best[0]):
            best = (r.fun, r.x); s = np.abs(r.x[:na]); rho = np.clip(np.abs(r.x[na:]), 0, 1); g, e = sl0gap(s, rho, AT, m)
            if g is not None: print(it, 'gap %.5f obj %.5f c %.4f tau %.4f d %.4f' % (g, r.fun, e['c'], e['tau'], e['d']), 's', np.round(s, 4).tolist(), 'rho', np.round(rho, 4).tolist(), flush=True)
    print('BEST', best[0] if best else None)
