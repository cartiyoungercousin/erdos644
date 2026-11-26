import sys, json, time, numpy as np
exec(open('dbg_master.py').read().split("print('oracle best U:'")[0])
pats = [({tuple([k[:-1], int(k[-1])]): v for k, v in P.items()}, PO) for P, PO in d['cert']]
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import coo_matrix
cap = {}
orig = jm.Model.solve
def grab(self, obj, tl=120, gap=1e-9): cap['m'] = self; return orig(self, obj, tl, gap)
jm.Model.solve = grab; jm.master2(S, m1, o1, pats, T, jm.SPEC); jm.Model.solve = orig
s = cap['m']; n = len(s.lb); A = coo_matrix((s.va, (s.ri, s.ci)), shape=(len(s.lo), n)).tocsr()
for opts in ({'presolve': False}, {'presolve': True, 'mip_rel_gap': 1e-4}, {'presolve': False, 'mip_rel_gap': 1e-4}):
    t0 = time.time()
    r = milp(np.zeros(n), constraints=LinearConstraint(A, s.lo, s.hi), integrality=np.array(s.it), bounds=Bounds(s.lb, s.ub), options=dict(opts, time_limit=170))
    print(opts, r.status, r.message[:40], '%.0fs' % (time.time() - t0))
