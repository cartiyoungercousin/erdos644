r"""Adversary-side search for one first request R1: try many legal answers M1 (voluntary live drops, every pad mix
on a grid) and decide each stage-2 game exactly (jm.stage2).  Any 'ADV' refutes R1.
usage: py -3.14 adv1_search.py alpha delta nproc step R1(comma list of 7)"""
import sys, os, json, time, itertools
import numpy as np
import multiprocessing as mp
import jm
AL, DE, NP, ST = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
R1 = [float(x) for x in sys.argv[5].split(',')]
S = jm.sizes(AL); T = 12 - DE; HERE = os.path.dirname(os.path.abspath(__file__))


def cands():
    room = {c: S[c] - R1[i] for i, c in enumerate(jm.C7)}
    def g(c, fine=False):
        m = room[c]
        if m <= 1e-9: return [0.0]
        v = set(np.round(np.arange(0, m + 1e-9, ST), 6)) | {m, max(0.0, m - 0.25), max(0.0, m - 0.5)}
        return sorted(x for x in v if 0 <= x <= m + 1e-9)
    out = set()
    for vals in itertools.product(*[g(c) for c in jm.C7]):
        s = sum(vals)
        if s > 14 + 1e-9: continue
        m1 = dict(zip(jm.C7, vals))
        if all(jm.in_spec(sum(m1[c] for c in cs), jm.SPEC, 1e-9) for cs in jm.MEM.values()):
            out.add(tuple(vals) + (round(14 - s, 6),))
    return sorted(out, key=lambda st: -sum(st[:4]))


def work(st):
    m1 = dict(zip(jm.C7, st[:7])); t0 = time.time()
    res, info, it, _ = jm.stage2(S, m1, st[7], T, jm.SPEC, maxit=120, tl=150)
    return st, res, it, round(time.time() - t0, 1), (info[2][0] if res == 'REQ' else None)


if __name__ == '__main__':
    cs = cands()[:int(os.environ.get("NMAX", "3000"))]; t0 = time.time()
    tag = '_'.join('%g' % x for x in R1)
    log = open(os.path.join(HERE, 'logs', 'adv1_a%g_d%g_%s.log' % (AL, DE, tag)), 'w')
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); log.write(s + '\n'); log.flush()
    P('R1 =', R1, 'alpha', AL, 't', T, ': %d legal candidate M1 on step %g' % (len(cs), ST))
    cnt = {}
    with mp.Pool(NP) as pool:
        for st, res, it, sec, U in pool.imap_unordered(work, cs):
            cnt[res] = cnt.get(res, 0) + 1
            if res != 'REQ': P('  M1', [round(x, 4) for x in st], res, 'it', it, sec)
            if res == 'ADV':
                P('REFUTED by M1 =', list(st)); pool.terminate(); break
    P('counts', cnt, '%.0fs' % (time.time() - t0))
