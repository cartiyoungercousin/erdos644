"""n-independent three-anchor finishes over ALL 715 seven-types (units of k).
Anchors x_a, x_b, x_c (a 'pencil': empty triple intersection) with Venn masses e_a,e_b,e_c (private parts) and
d_ab,d_ac,d_bc (pairwise-only parts), each anchor of mass 1. The rest Z of V (arbitrarily large) gets co-type
F = {a,b,c}, which must lie in M; so Z puts no load on the other four members. Every point of U = x_a u x_b u x_c
gets a co-type I in M with the forced trace I cap F (E_a -> F-{a}, D_bc -> {a}, ...). Each of the 4 other
members g needs load L_g = mass{x in U : g in I_x} <= t (then V - {x: g in I_x} has >= n - T points, contains a
member). Minimise t. Fano (class 706) gives t = |U|/2 = (3+w)/4 (Lemma P1, w = sum e).
usage: py -3.14 anchor3_lp.py NSAMPLES SEED NPROC -> logs/anchor3_<NSAMPLES>_<SEED>.log"""
import json, os, sys, itertools, random
import numpy as np
from scipy.optimize import linprog
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
rows = json.load(open(os.path.join(HERE, '..', '..', 'programme2', 'verify', 'out', 'maxint7_classes_lp.json')))
CLS = []
for i, r in enumerate(rows):
    if r['lp'] == 'None': continue
    v = int(r['mask'], 16)
    CLS.append((i, r['lp'], r['fano'], [S for S in range(128) if v >> S & 1]))

def solve(M, F, masses):
    """F = (a,b,c) ordered; masses = dict region->mass, regions 'Ea','Eb','Ec','Dab','Dac','Dbc'."""
    a, b, c = F
    Fm = (1 << a) | (1 << b) | (1 << c)
    if Fm not in set(M): return None
    trace = {'Ea': Fm & ~(1 << a), 'Eb': Fm & ~(1 << b), 'Ec': Fm & ~(1 << c),
             'Dbc': 1 << a, 'Dac': 1 << b, 'Dab': 1 << c}
    others = [g for g in range(7) if g not in F]
    var = []
    for R, tr in trace.items():
        if masses[R] <= 1e-12: continue
        opts = [I for I in M if I & Fm == tr]
        if not opts: return None
        var += [(R, I) for I in opts]
    nv = len(var) + 1
    cvec = np.zeros(nv); cvec[-1] = 1
    A_eq, b_eq = [], []
    for R in trace:
        if masses[R] <= 1e-12: continue
        A_eq.append([1.0 if v[0] == R else 0.0 for v in var] + [0.0]); b_eq.append(masses[R])
    A_ub = [[1.0 if v[1] >> g & 1 else 0.0 for v in var] + [-1.0] for g in others]
    res = linprog(cvec, A_ub=A_ub, b_ub=[0.0] * 4, A_eq=A_eq, b_eq=b_eq, bounds=[(0, None)] * nv, method='highs')
    return res.fun if res.status == 0 else None

def sample(rng):
    while True:
        dab, dac, dbc = rng.random() * 0.5, rng.random() * 0.5, rng.random() * 0.5
        if rng.random() < 0.3: dab, dac, dbc = [x * rng.random() for x in (dab, dac, dbc)]
        ea, eb, ec = 1 - dab - dac, 1 - dab - dbc, 1 - dac - dbc
        if min(ea, eb, ec) >= 0:
            return dict(Ea=ea, Eb=eb, Ec=ec, Dab=dab, Dac=dac, Dbc=dbc)

def job(args):
    ci, samples = args
    i, lp, fano, M = CLS[ci]
    best = [9.0] * len(samples)
    for F in itertools.permutations(range(7), 3):
        if F[0] > 0 and False: pass
        Fm = sum(1 << x for x in F)
        if Fm not in set(M): continue
        for s, ms in enumerate(samples):
            v = solve(M, F, ms)
            if v is not None and v < best[s]: best[s] = v
    return ci, best

if __name__ == '__main__':
    ns, seed, nproc = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    samples = [dict(Ea=0, Eb=0, Ec=0, Dab=.5, Dac=.5, Dbc=.5)] + [sample(rng) for _ in range(ns - 1)]
    with Pool(nproc) as p:
        res = dict(p.map(job, [(ci, samples) for ci in range(len(CLS))]))
    fano_ci = [ci for ci in range(len(CLS)) if CLS[ci][2]][0]
    out = open(os.path.join(HERE, 'logs', 'anchor3_%d_%d.log' % (ns, seed)), 'w')
    worst_gain = 0
    for s, ms in enumerate(samples):
        U = sum(ms.values()); w = ms['Ea'] + ms['Eb'] + ms['Ec']
        tf = res[fano_ci][s]
        bestnf = min((res[ci][s], CLS[ci][0]) for ci in range(len(CLS)) if ci != fano_ci)
        line = 'w=%.4f |U|/2=%.4f fano=%.4f best_nonfano=%.4f (class %d) gain=%.4f' % (w, U / 2, tf, bestnf[0], bestnf[1], tf - bestnf[0])
        worst_gain = max(worst_gain, tf - bestnf[0])
        print(line, file=out)
    print('max gain of a non-Fano type over Fano:', worst_gain, file=out)
    out.close()
    print('max gain', worst_gain)
