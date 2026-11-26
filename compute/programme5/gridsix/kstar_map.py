"""Adversary repair at K* = A(ka) | B(7) | OK(7 - ka) (K's spare mass on outside points), default ka = 20/3.
Map every certified alpha = 7 ADV state M1 to K* (A-part capped at ka; the excess moved to Gd, or to outside),
keep the S*-legal images, and decide each: (a) static drop-one frames (stage1g.best_static, exact SCIP) all > t,
(b) E-frame adaptive game jm.stage2 (SCIP-proved ADV).  K's outside cell OK is ignored by jm (his answers never
need it; her requests on it cannot help in the E-frame).  Output logs/kstar_states.jsonl.
usage: py kstar_map.py nproc [ka]"""
import sys, os, json, time
from multiprocessing import Pool
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'jointmilp'))
import jm
from stage1g import Stage1, sizes_K, SPEC

KA = float(sys.argv[2]) if len(sys.argv) > 2 else 20 / 3
SK = sizes_K(KA, 7.0, 0.0, 7.0 - KA)
SJ = {'X': 6.0, 'Y': 5.0, 'A': KA, 'B': 7.0, 'Ep': 3.0, 'Fd': 1.0, 'Gd': 9.0 - KA}
T = 12 - 0.002
C7 = jm.C7


def legal(m, o):
    if o < -1e-9 or abs(sum(m.values()) + o - 14) > 1e-6: return False
    if any(m[c] > SJ[c] + 1e-9 or m[c] < -1e-9 for c in C7): return False
    return all(jm.in_spec(sum(m[c] for c in cs), SPEC, 1e-7) for cs in jm.MEM.values())


def images(st):
    m = dict(zip(C7, st[:7])); o = st[7]; out = []
    ex = max(0.0, m['A'] - KA)
    for to in ('Gd', 'out'):
        mm = dict(m); mm['A'] -= ex; oo = o
        if to == 'Gd' and mm['Gd'] + ex <= SJ['Gd'] + 1e-9: mm['Gd'] += ex
        else: oo += ex
        if legal(mm, oo) and (mm, oo) not in out: out.append((mm, oo))
    return out


def work(st):
    res = []
    for m, o in images(st):
        s1 = Stage1(SK, {}, T, log=lambda *a: None)
        mm = dict(m); mm['OK'] = 0.0; mm['EpK'] = 0.0
        bs = s1.best_static(mm)
        ok = all(v is not None and v > T + 1e-6 for v in bs.values() if v is not None) and all(v is not None for v in bs.values())
        verdict = None
        if ok:
            verdict, info, it, _ = jm.stage2(SJ, m, o, T, SPEC, maxit=150, tl=100, wall=300)
        res.append({'src': st, 'M1': [m[c] for c in C7] + [o], 'static': bs, 'static_ok': ok, 'stage2': verdict})
        if ok and verdict == 'ADV': break
    return res


if __name__ == '__main__':
    NP = int(sys.argv[1])
    rows = [json.loads(l) for l in open('logs/states_static.jsonl')]
    sts = [r['M1'] for r in rows]
    out = open('logs/kstar_states.jsonl', 'w'); t0 = time.time(); cnt = {}
    with Pool(NP) as p:
        for i, res in enumerate(p.imap_unordered(work, sts, chunksize=4)):
            for r in res:
                out.write(json.dumps(r) + '\n')
                k = 'ADV' if (r['static_ok'] and r['stage2'] == 'ADV') else ('static_fail' if not r['static_ok'] else str(r['stage2']))
                cnt[k] = cnt.get(k, 0) + 1
            if i % 200 == 0: out.flush(); print(i, len(sts), cnt, round(time.time() - t0), flush=True)
    print('done', cnt, round(time.time() - t0), flush=True)
