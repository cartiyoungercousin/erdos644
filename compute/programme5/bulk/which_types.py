"""For each non-Fano-only two-cell family H_J (from programme4 fano_suff certs), find WHICH seven-types
(S7-classes of maximal intersecting families M on [7]) admit a good seven in H_J.
Criterion (monotone form, PROGRAMME4_CELLS §1): integers x^c_S >= 0 (S in the minimal sets of M, c = cell),
sum_S x^c_S = a_c, and for every m in [7] the region A_m = (sum_{S not containing m} x^c_S)_c dominates some
profile j in J. The condition is symmetric in m, so the labelling of M is irrelevant: one CP-SAT model per class.
usage: py -3.14 which_types.py LPMAX NPROC   -> logs/which_types_<LPMAX>.jsonl"""
import json, glob, os, sys, itertools
from fractions import Fraction as Fr
from multiprocessing import Pool
HERE = os.path.dirname(os.path.abspath(__file__))
CERTS = os.path.join(HERE, '..', '..', 'programme4', 'cells', 'certs')
rows = json.load(open(os.path.join(HERE, '..', '..', 'programme2', 'verify', 'out', 'maxint7_classes_lp.json')))
CL = []
for i, r in enumerate(rows):
    if r['lp'] == 'None': continue
    v = int(r['mask'], 16)
    sets = [S for S in range(128) if v >> S & 1]
    mins = [S for S in sets if not any(T != S and (T & S) == T for T in sets)]
    CL.append((i, Fr(r['lp']), r['fano'], mins))
CL.sort(key=lambda c: c[1])

def feasible(a, k, J1, mins):
    from ortools.sat.python import cp_model
    md = cp_model.CpModel()
    x = [[md.NewIntVar(0, a[c], '') for S in mins] for c in range(2)]
    for c in range(2): md.Add(sum(x[c]) == a[c])
    for m in range(7):
        idx = [t for t, S in enumerate(mins) if not S >> m & 1]
        bs = []
        for j1 in J1:
            b = md.NewBoolVar(''); bs.append(b)
            md.Add(sum(x[0][t] for t in idx) >= j1).OnlyEnforceIf(b)
            md.Add(sum(x[1][t] for t in idx) >= k - j1).OnlyEnforceIf(b)
        md.AddBoolOr(bs)
    s = cp_model.CpSolver(); s.parameters.num_workers = 1; s.parameters.max_time_in_seconds = 20
    st = s.Solve(md)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return 1, {format(S, '07b')[::-1]: [s.Value(x[0][t]), s.Value(x[1][t])] for t, S in enumerate(mins)
                   if s.Value(x[0][t]) + s.Value(x[1][t])}
    return (0 if st == cp_model.INFEASIBLE else -1), None

def job(fam):
    k, a, J1, tau, lpmax = fam
    out = []
    for (i, lp, fano, mins) in CL:
        if lp > lpmax: break
        if lp * k > sum(a): continue          # needs union >= LP(M) k
        ok, wit = feasible(a, k, J1, mins)
        if ok != 0: out.append((i, str(lp), fano, ok, wit))
    return dict(k=k, a=a, J1=J1, tau=tau, n=sum(a), types=out)

if __name__ == '__main__':
    lpmax = Fr(sys.argv[1]); nproc = int(sys.argv[2])
    fams = []; seen = set()
    for f in sorted(glob.glob(os.path.join(CERTS, 'fano_k*_T*_q2.jsonl'))):
        for line in open(f):
            r = json.loads(line)
            for w in r['nonfano_only']:
                J1 = sorted(set(j[0] for j in w['J']))
                key = (r['k'], tuple(r['a']), tuple(J1))
                if key in seen: continue
                seen.add(key); fams.append((r['k'], r['a'], J1, w['tau'], lpmax))
    print(len(fams), 'distinct families', flush=True)
    os.makedirs(os.path.join(HERE, 'logs'), exist_ok=True)
    with Pool(nproc) as p, open(os.path.join(HERE, 'logs', 'which_types_%s.jsonl' % str(lpmax).replace('/', '_')), 'w') as fo:
        for res in p.imap_unordered(job, fams):
            fo.write(json.dumps(res) + '\n'); fo.flush()
