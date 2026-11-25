import sys, time
from tau_star import *; import families as F
fam, orb = F.fkw(2); print(fam.name, len(fam.masks), min_transversal_size(fam))
for o in (orb, None):
    r = solve(fam, o, verbose=False); print({k: v for k, v in r.items() if k not in ('y','y_phi')})
r2 = solve(fam, orb, kind='ilp'); print('ilp', r2['tau_b'], r2['max_atom'], r2['phi'])
fam, orb = F.complete(16, 9); print(solve(fam, orb)['tau_b'], 16/8)
