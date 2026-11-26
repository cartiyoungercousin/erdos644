"""Passive-adversary certificate (caps every closure that keeps E,F,G and all later answers, of ANY depth).

After the first answer K the adversary plays passively: to a request R he answers M = (live \ R) u (points outside V),
or, if live \ R has mass > 1, any unit-mass part of it.  Then the pairs killed by M lie inside a set of mass
<= max(t, live - 1).  Hence if   live(E,F,G,K) <= 1 + t   and   t*_3(E,F,G,K) > t   (three static blocks, exact MILP,
keep all four), no continuation of any depth closes.  For each first request R1 (grid s1; Z always requested) we
look for such a K (exclusions on grid s1, hub-keeping first) and report the certified margin min_R1 max_K t*_3.
usage: py -3.14 passive.py delta s1 NPROC [stride offset]   (units k/14)"""
import sys, time, numpy as np
from multiprocessing import Pool
import engine, depth2
EPS = 1e-9; K14 = 14.0

def atoms4(C, R, e):
    at = [(6, 0.0, True)]
    for i, c in enumerate(depth2.ORDER):
        m = C[c] / K14; r = R[i] / K14; kin = (C[c] - R[i] - e[c]) / K14
        if m - r > EPS: at.append((depth2.TY[c] | 8, kin, True))
        at.append((depth2.TY[c], m - kin, True))
    return at

def live_mass(at, full=15):
    pres = [(ty, m) for ty, m, p in at if p]
    return sum(m for ty, m in pres if any((ty | u) == full for u, _ in pres if u != ty))

def work(args):
    C, R, t, s1, target = args
    tn = t / K14; best = (-1, None, None)
    for e in depth2.answers(C, R, t, s1):
        at = atoms4(C, R, e)
        lm = live_mass(at)
        if lm > 1 + tn + EPS: continue
        v = engine.finish(at, 15, 3)
        if v > best[0]: best = (v, e, lm)
        if v >= target - EPS: break
    return R, best

if __name__ == '__main__':
    delta, s1, NP = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
    stride, off = (int(sys.argv[4]), int(sys.argv[5])) if len(sys.argv) > 5 else (1, 0)
    t = 12.0 - delta; C = depth2.cells(6, 5)
    Rs = depth2.requests(C, t, s1)[off::stride]
    print('passive certificate: t=%g/14, %d first requests (grid %g, stride %d offset %d)' % (t, len(Rs), s1, stride, off), flush=True)
    t0 = time.time(); worst = (9, None); fails = []
    with Pool(NP) as p:
        for i, (R, (v, e, lm)) in enumerate(p.imap_unordered(work, [(C, R, t, s1, 12.0 / K14) for R in Rs], chunksize=8)):
            if v < worst[0]: worst = (v, R, e, lm)
            if v <= t / K14 + EPS: fails.append(R); print('  NOT CERTIFIED: R1=%s best t*_3=%.4f/14' % (R, v * K14), flush=True)
            if i % 250 == 0: print('  %d/%d  worst so far %.4f/14 at R1=%s K excl=%s live=%.3f  (%.0fs)' % (i, len(Rs), worst[0] * K14, worst[1], worst[2] if len(worst) > 2 else None, (worst[3] * K14) if len(worst) > 3 and worst[3] is not None else -1, time.time() - t0), flush=True)
    print('DONE: %d R1, not certified %d; min over R1 of best t*_3 = %.4f/14 at R1=%s, K excl %s, live %.3f/14 (%.0fs)'
          % (len(Rs), len(fails), worst[0] * K14, worst[1], worst[2], (worst[3] or 0) * K14, time.time() - t0), flush=True)
