"""Class A with the spectrum: every answer (K and L) must have all its traces on earlier members in S*
(S* of the depth-<=3 S-game, G = 168, t = 0.852: [0,46] u [60,73] u [79,167] /168, as closed intervals).
usage: py -3.14 run_AS.py delta s1 h NPROC"""
import sys, time, numpy as np
from multiprocessing import Pool
import fast2, depth2, run_A
EPS = 1e-9; K14 = 14.0
SINT = [(0, 46 / 168), (60 / 168, 73 / 168), (79 / 168, 167 / 168)]
inS = lambda v: any(a - 1e-9 <= v <= b + 1e-9 for a, b in SINT)

def work(args):
    C, R, t, s1, h = args; tn = t / K14
    for e in run_A.k_answers(C, R, t, s1):
        kin = {c: C[c] - R[i] - e[c] for i, c in enumerate(depth2.ORDER)}
        trE = (kin['X'] + kin['Y'] + kin['E']) / K14; trF = (kin['X'] + kin['F']) / K14; trG = (kin['Y'] + kin['G']) / K14
        if not (inS(trE) and inS(trF) and inS(trG)): continue
        P = depth2.pos4(C, R, e)
        v, R2, L2 = fast2.depth1xS(P, tn, h / K14, SINT, want=tn)
        if v > tn + EPS: return (R, e, v * K14, (trE, trF, trG))
    return (R, None, None, None)

if __name__ == '__main__':
    delta, s1, h, NP = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    t = 12.0 - delta; C = depth2.cells(6, 5); extra = t - 11
    Rs = []
    for a in depth2.grid(min(extra, C['E']), s1):
        for b in depth2.grid(min(extra - a, C['F']), s1):
            c = extra - a - b
            if -EPS <= c <= C['G'] + EPS: Rs.append((6.0, 5.0, a, b, max(0.0, c)))
    print('class A + spectrum S*: t=%g/14, %d first requests, K grid %g, R2 grid %g' % (t, len(Rs), s1, h), flush=True)
    t0 = time.time(); ok = 0
    with Pool(NP) as p:
        for (R, e, v, tr) in p.imap_unordered(work, [(C, R, t, s1, h) for R in Rs]):
            ok += e is not None
            print('  R1 extra (E,F,G)=%s: %s' % (R[2:], ('SPOILED by K excl %s (traces %.3f %.3f %.3f), value %.4f' % ({c: e[c] for c in 'EFG'}, tr[0], tr[1], tr[2], v)) if e else 'NO SPOILER'), flush=True)
    print('spoiled %d / %d (%.0fs)' % (ok, len(Rs), time.time() - t0), flush=True)
