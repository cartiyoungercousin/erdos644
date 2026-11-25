r"""PETAL §41.2: test SL0 (exists A with h(A) <= tau and beta(A) <= d) on random unions of arena classes, exact LP:
min beta s.t. beta >= rho_i + |R_i \ A|, |A| - 1 + beta <= tau."""
import sys, numpy as np
from scipy.optimize import linprog
from multiarena import atoms, evaluate
t = float(sys.argv[1]); m = int(sys.argv[2]); trials = int(sys.argv[3]); rng = np.random.default_rng(int(sys.argv[4]))
filt = len(sys.argv) > 5
theta = (6 * t - 2) / 5; cmax = 1 - 5 * t / 9; AT = atoms(m); na = len(AT)
R = np.array([[1.0 if i in S else 0.0 for S in AT] for i in range(m)])
worst = -9; n = 0; wrec = None
for _ in range(trials):
    core = rng.uniform(0.5, 1.4)
    s = np.array([core if len(S) == m else rng.exponential(0.4 / m) * (rng.random() < 0.6) for S in AT]); rho = rng.random(m) * 0.3
    e = evaluate(s, rho, t, AT, m)
    if e is None or e['c'] <= 0.02: continue
    if filt and not (theta < e['c'] < cmax and e['tau'] >= t / 2): continue
    n += 1; tau, d = e['tau'], e['d']
    Aub = [np.r_[-R[i], -1.0] for i in range(m)]; bub = [-rho[i] - R[i] @ s for i in range(m)]
    Aub.append(np.r_[np.ones(na), 1.0]); bub.append(1 + tau)
    r = linprog(np.r_[np.zeros(na), 1.0], A_ub=np.array(Aub), b_ub=np.array(bub), bounds=[(0, x) for x in s] + [(0, None)], method='highs')
    gap = r.fun - d
    if gap > worst: worst = gap; wrec = (np.round(s, 4).tolist(), np.round(rho, 4).tolist(), round(e['c'], 4), round(tau, 4), round(d, 4))
print('t', t, 'm', m, 'instances', n, 'max(min beta at h<=tau  -  d) = %.6f' % worst, wrec)
