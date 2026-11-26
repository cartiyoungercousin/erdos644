"""Static finishes of every frame after each certified ADV M1 state of the joint MILP (exploratory)."""
import json, sys, time
from frames import base_sizes, refine, alive, ZEPS
from cover import min_t, check
C7 = ['X','Y','A','B','Ep','Fd','Gd']
src = '../jointmilp/logs/cover_v3_a7_d0.002.jsonl'
lim = int(sys.argv[1]); step = int(sys.argv[2]) if len(sys.argv) > 2 else 1
FR = {'EFGKM1': (['E','F','G','K','M1'], 2), 'FGKM1': (['F','G','K','M1'], 3), 'EGKM1': (['E','G','K','M1'], 3),
      'EFKM1': (['E','F','K','M1'], 3), 'EFGM1': (['E','F','G','M1'], 3)}
n = 0; t0 = time.time(); best = {}
for li, line in enumerate(open(src)):
    if li % step: continue
    d = json.loads(line)
    if d['res'] != 'ADV': continue
    m1 = dict(zip(C7, d['M1'][:7])); m1['Z'] = ZEPS / 2
    at = refine(base_sizes(7.0), [{(c,): v for c, v in m1.items()}])
    vals = {}
    for nm, (fr, r) in FR.items():
        al = alive(at, fr); sz = {a: s for a, s in at.items() if s > 1e-9}
        tt, pl = min_t(sz, al, r, tl=30)
        vals[nm] = round(tt, 3) if tt is not None else None
    print(li, [round(x, 3) for x in d['M1']], vals, flush=True)
    n += 1
    if n >= lim: break
print('time', time.time() - t0)
