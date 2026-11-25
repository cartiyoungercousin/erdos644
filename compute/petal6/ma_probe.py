"""PETAL §41.2 probe: on random unions of arena classes, compare the LP-optimal region with A = union of regions
and with A = single regions, against the arena bound tau + (8/3) d (first branch h + 8beta/3)."""
import sys, numpy as np
from multiarena import atoms, evaluate
t = float(sys.argv[1]); m = int(sys.argv[2]); trials = int(sys.argv[3]); rng = np.random.default_rng(int(sys.argv[4]))
theta = (6 * t - 2) / 5; cmax = 1 - 5 * t / 9; AT = atoms(m)
R = np.array([[1.0 if i in S else 0.0 for S in AT] for i in range(m)])
worstU = -9; worstLP = -9; worstbest = -9; n = 0
for _ in range(trials):
    core = rng.uniform(0.7, 1.3)
    s = np.array([core if len(S) == m else rng.exponential(0.3 / m) * (rng.random() < 0.6) for S in AT]); rho = rng.random(m) * 0.15
    e = evaluate(s, rho, t, AT, m)
    if e is None or not (theta < e['c'] < cmax and e['tau'] >= t / 2): continue
    n += 1; tau, d, c = e['tau'], e['d'], e['c']
    tgt = tau + 8 * d / 3
    U = (R.sum(0) > 0) @ s; bU = rho.max(); hU = U - 1 + bU
    costs = [hU + 8 * bU / 3]
    for i in range(m):   # A = R_i: beta = max_j rho_j + |R_j \ R_i|
        b = max(rho[j] + ((R[j] > 0) & (R[i] == 0)) @ s for j in range(m)); h = R[i] @ s - 1 + b; costs.append(h + 8 * b / 3)
    # LP optimum of first branch only, from evaluate's x
    hl = e['x'].sum() - 1 + e['beta']; lp = hl + 8 * e['beta'] / 3
    worstU = max(worstU, costs[0] - tgt); worstLP = max(worstLP, lp - tgt); worstbest = max(worstbest, min(costs) - tgt)
print('t', t, 'm', m, 'feasible', n, 'max(cost(U) - tgt) %.5f  max(min over U,R_i - tgt) %.5f  max(LP - tgt) %.5f' % (worstU, worstbest, worstLP))
