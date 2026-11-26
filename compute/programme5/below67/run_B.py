"""Class B: first requests missing part of the hubs X u Y (Z always requested).  For each sampled R1 (grid s1), try his
answers K (all exclusion vectors on grid s1, hub-keeping first) until one is a spoiler: every structured R2
(pool1.structured_requests: any set of live types requested fully plus one or two partial fills) is refuted by an exact
MILP two-block value > t at some answer L.  [Her R2 side: structured family, not exhaustive.]
usage: py -3.14 run_B.py delta s1 nsample seed NPROC"""
import sys, time, random, numpy as np
from multiprocessing import Pool
import depth2, pool1
EPS = 1e-9; K14 = 14.0

def work(args):
    C, R, t, s1, seed = args
    tn = t / K14; rng = np.random.default_rng(seed)
    tried = 0
    for e in depth2.answers(C, R, t, s1):
        tried += 1
        P = depth2.pos4(C, R, e)
        reqs = pool1.structured_requests(P, tn)
        reqs.sort(key=lambda r: -np.sum(r > EPS))
        closed = None
        for r in reqs:
            v, L = pool1.refute(P, tn, r, rng)
            if v <= tn + EPS: closed = r; break
        if closed is None:
            return (R, e, tried, len(reqs))
        if tried >= 400: break
    return (R, None, tried, 0)

if __name__ == '__main__':
    delta, s1, ns, seed, NP = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
    t = 12.0 - delta; C = depth2.cells(6, 5)
    Rs = [R for R in depth2.requests(C, t, s1) if not (R[0] >= 6 - EPS and R[1] >= 5 - EPS)]
    random.seed(seed); S = random.sample(Rs, min(ns, len(Rs)))
    print('class B: t=%g/14, %d first requests on grid %g, sample %d' % (t, len(Rs), s1, len(S)), flush=True)
    t0 = time.time(); ok = 0; cand = []
    with Pool(NP) as p:
        for (R, e, tried, nr) in p.imap_unordered(work, [(C, R, t, s1, i) for i, R in enumerate(S)]):
            if e is not None:
                ok += 1; print('  R1 %s: SPOILED by K excl %s (answer #%d; all %d structured R2 refuted)' % (R, e, tried, nr), flush=True)
            else:
                cand.append(R); print('  R1 %s: NO SPOILER among %d answers (candidate)' % (R, tried), flush=True)
    print('spoiled %d / %d, candidates %s  (%.0fs)' % (ok, len(S), cand, time.time() - t0), flush=True)
