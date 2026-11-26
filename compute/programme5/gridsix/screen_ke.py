"""Requester-side screen against the repaired K_e = A(a) | B(7) | (E'&K)(7-a) (default a = 20/3).
For each candidate first request R1 (cells X,Y,A,B,Ep,EpK,Fd,Gd; |R1| <= t): exact stage-1 CEGAR with the static
drop-one frames (stage1g, SCIP).  INVULNERABLE answers are then decided in the E-frame game by jm.stage2 in the
sound model (jm sees only E'-K; his answers never use E'&K points; an ADV is sound, a REQ is not certified).
usage: py screen_ke.py nproc tag [a] [nrand] [seed]   -> logs/screen_<tag>.jsonl"""
import sys, os, json, time, random
from multiprocessing import Pool
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'jointmilp'))
import jm
from stage1g import Stage1, sizes_K
T = 12 - 0.002
A_ = float(sys.argv[3]) if len(sys.argv) > 3 else 20 / 3
SK = sizes_K(A_, 7.0, 7 - A_, 0.0)
FREE = ['X', 'Y', 'A', 'B', 'Ep', 'EpK', 'Fd', 'Gd']

def cands(nrand, seed):
    h = SK['EpK']; out = []
    base = [{'Y': T - 7, 'B': 7}, {'X': T - A_, 'A': A_}, {'A': A_, 'X': 3, 'B': 1, 'Y': T - A_ - 4},
            {'Y': 5, 'B': T - 5}, {'X': 6, 'A': T - 6}]
    for b in base:
        out.append(dict(b))
        for take in ('Y', 'X', 'B', 'A'):              # make room for the hub E'&K
            if b.get(take, 0) >= h:
                c = dict(b); c[take] -= h; c['EpK'] = h; out.append(c)
    # hub + E' + structured halves
    for x, y, a, b in [(6, 0, 0, 5.665), (0, 5, 6.665, 0), (3, 2.5, 3.333, 2.832), (6, 5, 0, 0.665), (0, 0, 6.667, 5.0),
                       (2, 2, 4, 3.665), (4, 1, 2, 4.665), (1, 4, 4.665, 2)]:
        c = {'X': x, 'Y': y, 'A': a, 'B': b, 'EpK': h}; s = sum(c.values())
        if s <= T + 1e-9: out.append(c)
    rng = random.Random(seed)
    for _ in range(nrand):
        c = {}; left = T
        cells = FREE[:]; rng.shuffle(cells)
        if rng.random() < 0.7: cells.remove('EpK'); cells.insert(0, 'EpK')
        for cc in cells:
            v = min(SK[cc], left) if rng.random() < 0.45 else min(SK[cc], left, round(rng.uniform(0, SK[cc]) * 3) / 3)
            if v > 1e-9: c[cc] = round(v, 6); left -= v
            if left <= 1e-9: break
        out.append(c)
    uniq = []
    for c in out:
        c = {k: v for k, v in c.items() if v > 1e-9}
        if c not in uniq and sum(c.values()) <= T + 1e-6: uniq.append(c)
    return uniq

def work(r1):
    s1 = Stage1(SK, r1, T, log=lambda *x: None); t0 = time.time()
    res, info = s1.run(maxit=160)
    out = {'R1': r1, 'stage1': res, 'sec': round(time.time() - t0)}
    if res == 'INFEASIBLE':
        s1.dump('logs/kec_%s.json' % '_'.join('%s%g' % (k, round(v, 3)) for k, v in sorted(r1.items())), res)
    if res == 'INVULNERABLE':
        m, o, bs = info
        SJ = {'X': 6.0, 'Y': 5.0, 'A': A_, 'B': 7.0, 'Ep': SK['Ep'], 'Fd': 1.0, 'Gd': 9 - A_}
        m1 = {c: m.get(c, 0.0) for c in jm.C7}
        v, inf, it, _ = jm.stage2(SJ, m1, o + m.get('OK', 0.0), T, jm.SPEC, maxit=150, tl=100, wall=400)
        out.update({'M1': m, 'o1': o, 'static': bs, 'stage2': v})
    return out

if __name__ == '__main__':
    NP = int(sys.argv[1]); tag = sys.argv[2]
    nr = int(sys.argv[4]) if len(sys.argv) > 4 else 60; seed = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    C = cands(nr, seed); print('candidates', len(C), flush=True)
    out = open('logs/screen_%s.jsonl' % tag, 'w'); t0 = time.time()
    with Pool(NP) as p:
        for o in p.imap_unordered(work, C):
            out.write(json.dumps(o) + chr(10)); out.flush()
            print('[%ds] %s -> %s %s' % (time.time() - t0, {k: round(v, 3) for k, v in o['R1'].items()}, o['stage1'],
                                         o.get('stage2', '')), flush=True)
    print('done', flush=True)
