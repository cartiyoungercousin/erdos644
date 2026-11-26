"""Scan of the forced K family K = A(a) | B(7) | spare (7 - a) on outside points ('o') or on E' ('e'), a in
[20/3, 7]: exact stage-1 (static drop-one frames) for a few first requests R1 per K; an INVULNERABLE M1 is then
checked in the E-frame game (jm.stage2).  usage: py ascan.py nproc  -> logs/ascan.jsonl"""
import sys, os, json, time
from multiprocessing import Pool
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'jointmilp'))
import jm
from stage1g import Stage1, sizes_K, CELLS
T = 12 - 0.002
def R1s(a):
    return {'YB': {'Y': T - 7.0, 'B': 7.0}, 'XA': {'X': T - a, 'A': a},
            'AX3YB1': {'A': a, 'X': 3.0, 'B': 1.0, 'Y': T - a - 4.0}}
def work(job):
    a, kind, name = job
    S = sizes_K(a, 7.0, (7 - a) if kind == 'e' else 0.0, (7 - a) if kind == 'o' else 0.0)
    r1 = R1s(a)[name]; s1 = Stage1(S, r1, T, log=lambda *x: None); t0 = time.time()
    res, info = s1.run(maxit=250)
    out = {'a': a, 'spare': kind, 'R1': name, 'r1': r1, 'stage1': res, 'sec': round(time.time() - t0)}
    tag = 'ascan_%s_%s_%s' % (round(a, 4), kind, name)
    s1.dump('logs/%s.json' % tag, res, info)
    if res == 'INVULNERABLE':
        m, o, bs = info
        SJ = {'X': 6.0, 'Y': 5.0, 'A': a, 'B': 7.0, 'Ep': 3.0, 'Fd': 1.0, 'Gd': 9.0 - a}
        m1 = {c: m.get(c, 0.0) for c in jm.C7}; m1['Ep'] += m.get('EpK', 0.0); o1 = o + m.get('OK', 0.0)
        v, inf, it, _ = jm.stage2(SJ, m1, o1, T, jm.SPEC, maxit=150, tl=100, wall=400)
        out.update({'M1': m, 'o1': o, 'static': bs, 'stage2': v})
    return out
if __name__ == '__main__':
    AS = [float(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [20 / 3, 6.7, 6.75, 6.8, 6.9, 7.0]
    jobs = [(a, k, n) for a in AS for k in ('o', 'e') for n in ('YB', 'XA', 'AX3YB1')
            if not (a == 7.0 and k == 'e')]
    out = open('logs/ascan%s.jsonl' % (sys.argv[3] if len(sys.argv) > 3 else ''), 'w'); t0 = time.time()
    with Pool(int(sys.argv[1])) as p:
        for o in p.imap_unordered(work, jobs):
            out.write(json.dumps(o) + chr(10)); out.flush()
            print('[%ds] a=%.4f spare=%s R1=%s -> %s %s' % (time.time() - t0, o['a'], o['spare'], o['R1'], o['stage1'], o.get('stage2', '')), flush=True)
    print('done', flush=True)
