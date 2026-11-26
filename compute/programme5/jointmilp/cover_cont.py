r"""Continuous first requests.  Refuted M1 states (logs/cover_<tag>.jsonl, res == 'ADV') refute every R1 they avoid.
MILP: is there a request R1 (any real amounts, |R1| <= t, on the 7 cells) that NO refuted state avoids?  If yes,
compute his candidate answers to it, decide their stage-2 games (jm.stage2) and repeat; if no, every continuous
first request is refuted.  usage: py -3.14 cover_cont.py alpha delta nproc [maxrounds]"""
import sys, os, json, time
import numpy as np
import multiprocessing as mp
import jm

AL, DE, NP = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
MAXR = int(sys.argv[4]) if len(sys.argv) > 4 else 200
S = jm.sizes(AL); T = 12 - DE; SPEC = jm.SPEC
HERE = os.path.dirname(os.path.abspath(__file__))
WP = {'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3}
WEIGHTS = [None, {'X': 1, 'Y': 1, 'A': 1.3, 'B': 1.3}, {'X': 1.3, 'Y': 1.3, 'A': 1, 'B': 1},
           {'X': 1, 'Y': 1.3, 'A': 1.3, 'B': 1}, {'X': 1.3, 'Y': 1, 'A': 1, 'B': 1.3}]
EPSR = 1e-5


def uncovered(states, obj=None):
    m = jm.Model(); r = {c: m.v(0, S[c]) for c in jm.C7}
    m.row(jm.ex(*[(1, r[c]) for c in jm.C7]), -np.inf, T)
    for st in states:
        bs = []
        for i, c in enumerate(jm.C7):
            if st[i] <= EPSR: continue
            b = m.b(); bs.append(b)
            lo = S[c] - st[i] + EPSR                 # b=1 -> r_c >= |c| - m1_c + eps (R1 meets M1 in cell c)
            m.row(jm.ex((1, r[c]), (-lo, b)), 0)
        if not bs: return None
        m.row(jm.ex(*[(1, b) for b in bs]), 1)
    res = m.solve({} if obj is None else {next(iter(r[c])): obj[i] for i, c in enumerate(jm.C7)}, 170)
    if res.status == 2: return None
    if res.status != 0: return 'TIMEOUT'
    return [jm.val(res.x, r[c]) for c in jm.C7]


def decide(st):
    m1 = dict(zip(jm.C7, st[:7])); o1 = st[7]; t0 = time.time()
    res, info, it, _ = jm.stage2(S, m1, o1, T, SPEC, maxit=120, tl=150)
    out = {'M1': list(st), 'res': res, 'it': it, 'sec': round(time.time() - t0, 1), 'src': 'cont'}
    if res == 'ADV': out['cert'] = [[{'%s%d' % k: v for k, v in P.items() if v > 0}, PO] for P, PO in info]
    if res in ('REQ', 'ORACLE_FAIL'): out['R2'] = [{'%s%d' % k: v for k, v in info[0].items() if v > 1e-7}, info[1], info[2][0]]
    return out


if __name__ == '__main__':
    tag = 'a%g_d%g' % (AL, DE); fn = os.path.join(HERE, 'logs', 'cover_%s.jsonl' % tag)
    logf = open(os.path.join(HERE, 'logs', 'cover_cont_%s.log' % tag), 'a')
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); logf.write(s + '\n'); logf.flush()
    adv, bad = [], set(); t0 = time.time()
    for line in open(fn):
        d = json.loads(line)
        if d['res'] == 'ADV': adv.append(tuple(d['M1']))
        elif d['res'] == 'REQ': bad.add(tuple(d['M1']))        # '?'/ORACLE_FAIL states are retried
    P('alpha=%g t=%g: %d refuted states loaded' % (AL, T, len(adv)))
    with mp.Pool(NP) as pool, open(fn, 'a') as f:
        for rnd in range(MAXR):
            r1 = uncovered(adv)
            if r1 is None: P('ROUND %d: NO continuous R1 escapes the %d refuted states  => all R1 refuted (%.0fs)' % (rnd, len(adv), time.time() - t0)); break
            if r1 == 'TIMEOUT': P('cover MILP timeout'); break
            R1s = [r1]
            for j in range(NP - 1):                       # more escaping requests, random directions
                rr = uncovered(adv, obj=list(np.random.default_rng(rnd * 100 + j).normal(size=7)))
                if isinstance(rr, list) and all(max(abs(a - b) for a, b in zip(rr, q)) > 1e-3 for q in R1s): R1s.append(rr)
            P('round %d: %d uncovered R1, e.g. %s' % (rnd, len(R1s), [round(x, 4) for x in r1]))
            cands = []
            for rq in R1s:
                for w in WEIGHTS:
                    o = jm.oracle1(S, dict(zip(jm.C7, rq)), SPEC, w=w, wpad=WP)
                    if o is None: continue
                    st = tuple(round(o[0][c], 6) for c in jm.C7) + (round(o[1], 6),)
                    if st not in bad and st not in adv and st not in cands: cands.append(st)
            if not cands: P('  no new candidate M1 for these R1: OPEN', R1s); break
            outs = pool.map(decide, cands)
            got = False
            for out in outs:
                f.write(json.dumps(out) + '\n'); f.flush()
                if out['res'] == 'ADV': adv.append(tuple(out['M1'])); got = True
                else: bad.add(tuple(out['M1'])); P('  M1', out['M1'], '->', out['res'], out.get('R2'))
            if got: P('  refuted by %d new state(s) (%.0fs)' % (sum(o['res'] == 'ADV' for o in outs), time.time() - t0))
            if not got: P('  R1 NOT REFUTED by any candidate M1: OPEN ->', r1); break
