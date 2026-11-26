"""For every certified ADV M1 state of the joint MILP (logs/cover_v3_a7_d0.002.jsonl): static finishes of the
drop-one frames {F,G,K,M1}, {E,G,K,M1}, {E,F,K,M1}, {E,F,G,M1} with 3 requests (and {E,F,G,K,M1} with 2), exact
cell MILP (SCIP).  Z = F&G is a 0+ cell split 1:1 by M1 (worst case for her).  Output: logs/states_static.jsonl"""
import json, sys, time
from multiprocessing import Pool
from frames import base_sizes, refine, alive, ZEPS
from cover import min_t
C7 = ['X','Y','A','B','Ep','Fd','Gd']
FR = {'EFGKM1': (['E','F','G','K','M1'], 2), 'FGKM1': (['F','G','K','M1'], 3), 'EGKM1': (['E','G','K','M1'], 3),
      'EFKM1': (['E','F','K','M1'], 3), 'EFGM1': (['E','F','G','M1'], 3)}
def work(item):
    li, M1 = item
    m1 = dict(zip(C7, M1[:7])); m1['Z'] = ZEPS / 2
    at = refine(base_sizes(7.0), [{(c,): v for c, v in m1.items()}])
    sz = {a: s for a, s in at.items() if s > 1e-9}
    vals = {}
    for nm, (fr, r) in FR.items():
        tt, pl = min_t(sz, alive(at, fr), r, tl=60)
        vals[nm] = tt
    return {'line': li, 'M1': M1, 'static': vals}
if __name__ == '__main__':
    src = '../jointmilp/logs/cover_v3_a7_d0.002.jsonl'
    items = []
    for li, line in enumerate(open(src)):
        d = json.loads(line)
        if d['res'] == 'ADV': items.append((li, d['M1']))
    out = open('logs/states_static.jsonl', 'w'); t0 = time.time()
    with Pool(int(sys.argv[1])) as p:
        for i, r in enumerate(p.imap_unordered(work, items, chunksize=8)):
            out.write(json.dumps(r) + '\n')
            if i % 500 == 0: print(i, len(items), round(time.time() - t0), flush=True); out.flush()
    out.close(); print('done', len(items), round(time.time() - t0))
