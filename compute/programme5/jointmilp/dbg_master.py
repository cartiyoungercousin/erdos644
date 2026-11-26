import sys, json, jm, numpy as np
sys.argv = [sys.argv[0], "7", "0.002", "0", "0"]
from verify_cert import answer, S, T
st = [6.0, 0.0, 6.75, 0.002, 0.0, 0.0, 0.0, 1.248]
d = [json.loads(l) for l in open('logs/cover_a7_d0.002.jsonl') if '"save_cert"' in l][0]
m1 = dict(zip(jm.C7, st[:7])); o1 = st[7]; sz = jm.refined(S, m1, o1)
R2 = {('X', 1): 6.0, ('B', 1): 0.002, ('A', 1): 3.0842656079674837, ('A', 0): 0.023457954835815115, ('Y', 0): 2.8882764371967005}
print('oracle best U:', jm.oracle2(S, m1, o1, R2, 0.0, T, jm.SPEC)[0])
pats = [({tuple([k[:-1], int(k[-1])]): v for k, v in P.items()}, PO) for P, PO in d['cert']]
vals = [answer(P, PO, sz, o1, R2, 0.0) for P, PO in d['cert']]
print('patterns', len(pats), 'verifier: legal ones', sum(v is not None for v in vals), 'max U', max(v or -1 for v in vals))
def fix(m, r, rO):
    for k in r: m.row(r[k], R2.get(k, 0.0) - 1e-9, R2.get(k, 0.0) + 1e-9)
    m.row(rO, 0, 1e-9)
print('master with R2 fixed, all patterns:', 'INFEASIBLE' if jm.master2(S, m1, o1, pats, T, jm.SPEC, fix=fix) is None else 'feasible')
for i, p in enumerate(pats):
    if jm.master2(S, m1, o1, [p], T, jm.SPEC, fix=fix) is None:
        print(' pattern', i, 'alone blocks; verifier value', vals[i], d['cert'][i]); break
import time
orig = jm.Model.solve
for name, fn in (('highs', lambda self, obj, tl=120, gap=1e-9: orig(self, obj, tl, gap)),
                 ('scip', lambda self, obj, tl=120, gap=1e-9: self.solve_ortools(np.zeros(len(self.lb)), tl))):
    jm.Model.solve = fn; t0 = time.time()
    r = jm.master2(S, m1, o1, pats, T, jm.SPEC, tl=170)
    print(name, 'free master:', 'INFEASIBLE' if r is None else ('TIMEOUT' if r == 'TIMEOUT' else 'feasible'), '%.0fs' % (time.time() - t0))
jm.Model.solve = orig
