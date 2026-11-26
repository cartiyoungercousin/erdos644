"""Exact stage-1 (static drop-one frames) + E-frame check at K* for the grid requests left unrefuted by the mapped
states, largest first; a found invulnerable+ADV M1 is added and refutes every request it avoids.
usage: py kstar_resid.py unrefuted.json nproc [ka] [kind: o|e]"""
import sys, os, json, time
import numpy as np
from multiprocessing import Pool
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'jointmilp'))
import jm
from stage1g import Stage1, sizes_K
KA = float(sys.argv[3]) if len(sys.argv) > 3 else 20 / 3; KIND = sys.argv[4] if len(sys.argv) > 4 else 'o'
SK = sizes_K(KA, 7.0, (7 - KA) if KIND == 'e' else 0.0, (7 - KA) if KIND == 'o' else 0.0)
SJ = {'X': 6.0, 'Y': 5.0, 'A': KA, 'B': 7.0, 'Ep': 3.0, 'Fd': 1.0, 'Gd': 9.0 - KA}
if KIND == 'e': SJ['Ep'] = 3.0
T = 12 - 0.002; C7 = jm.C7
def work(r):
    r1 = dict(zip(C7, r)); s1 = Stage1(SK, r1, T, log=lambda *a: None); t0 = time.time()
    res, info = s1.run(maxit=200)
    out = {'R1': list(r), 'stage1': res, 'sec': round(time.time() - t0)}
    if res == 'INVULNERABLE':
        m, o, bs = info
        m1 = {c: m.get(c, 0.0) for c in C7}; m1['Ep'] += m.get('EpK', 0.0); o1 = o + m.get('OK', 0.0)
        v, inf, it, _ = jm.stage2(SJ, m1, o1, T, jm.SPEC, maxit=150, tl=100, wall=400)
        out.update({'M1': [m1[c] for c in C7] + [o1], 'static': bs, 'stage2': v})
    if res == 'INFEASIBLE':
        s1.dump('logs/kstar_close_%s.json' % '_'.join('%g' % x for x in r), res)
    return out
if __name__ == '__main__':
    reqs = np.array(json.load(open(sys.argv[1]))); NP = int(sys.argv[2])
    order = list(np.argsort(-reqs.sum(1))); left = np.ones(len(reqs), bool)
    SV = np.array([SJ[c] for c in C7]); out = open('logs/kstar_resid.jsonl', 'a'); t0 = time.time()
    with Pool(NP) as p:
        pending = {}; it = iter(order)
        def submit():
            for i in it:
                if left[i]:
                    left[i] = False; pending[i] = p.apply_async(work, (list(map(float, reqs[i])),)); return True
            return False
        for _ in range(NP): submit()
        while pending:
            time.sleep(1)
            for i in [i for i, a in pending.items() if a.ready()]:
                o = pending.pop(i).get()
                out.write(json.dumps(o) + chr(10)); out.flush()
                if o.get('stage2') == 'ADV':
                    m = np.array(o['M1'][:7]); cov = np.all(m[None, :] + reqs <= SV + 1e-6, axis=1); left &= ~cov
                print('[%ds] R1 %s -> %s %s ; left %d' % (time.time() - t0, o['R1'], o['stage1'], o.get('stage2', ''), left.sum()), flush=True)
                submit()
    print('done', flush=True)
