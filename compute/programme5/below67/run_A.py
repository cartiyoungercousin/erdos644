"""Class A (hub-complete first request, rule R0): R1 = X u Y u Z + extra (t - x - y) spread over E',F',G' (grid s1).
For every such R1 find a spoiling answer K (exclusions on E',F',G' remainders, grid s1, critical ones first) whose
depth-1 value (her R2 on grid h over live types, maximal; his L exact MILP; two blocks, keep all) exceeds t.
Then, at the spoiled state, also test the discard finishes (keep 4 + 3 blocks, keep 3 + 4 blocks; exact MILP) against
his keep-all-best L for every grid R2 (a closure there would only be a candidate).
usage: py -3.14 run_A.py delta s1 h NPROC [x14 y14]   (units k/14)"""
import sys, itertools, time, numpy as np
from multiprocessing import Pool
import fast2, engine, depth2
EPS = 1e-9; K14 = 14.0

def k_answers(C, R, t, s):
    ans = depth2.answers(C, R, t, s)
    ans = [e for e in ans if e['X'] + e['Y'] <= EPS]
    a0 = lambda e: C['G'] - R[4] - e['G']; b0 = lambda e: C['F'] - R[3] - e['F']
    # critical first: alpha > t - x, beta > t - y, and alpha+beta large
    ans.sort(key=lambda e: (-(min(a0(e) - (t - C['X']), b0(e) - (t - C['Y'])) > 0), -(a0(e) + b0(e))))
    return ans

def leaf_discards(C, R, e, R2, L2, P):
    """full 5-member position after K (from e) and L (in-masses L2 on live types; dead types: L takes nothing)"""
    atoms = [(6, 0.0, True)]
    for i, c in enumerate(depth2.ORDER):
        m = C[c] / K14; r = R[i] / K14; kin = m - r - e[c] / K14
        if kin > EPS or m - r > EPS: atoms.append((depth2.TY[c] | 8, kin, True))
        atoms.append((depth2.TY[c], m - kin, True))
    live = P.live
    out = []
    for (ty, m, p) in atoms:
        if ty in live:
            i = live.index(ty); lin = L2[i]
            full = R2[i] >= m - EPS and m > EPS
            if not full: out.append((ty | 16, lin, True))
            out.append((ty, m - lin, True))
        else:
            out.append((ty, m, True))
    return engine.best_finish(out, 5)

def work(args):
    C, R, t, s1, h = args
    tn = t / K14
    for e in k_answers(C, R, t, s1):
        P = depth2.pos4(C, R, e)
        v, R2, L2 = fast2.depth1x(P, tn, h / K14, want=tn)
        if v > tn + EPS:
            return (R, e, v * K14)
    return (R, None, None)

if __name__ == '__main__':
    delta, s1, h, NP = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    x14, y14 = (float(sys.argv[5]), float(sys.argv[6])) if len(sys.argv) > 6 else (6.0, 5.0)
    t = 12.0 - delta; C = depth2.cells(x14, y14)
    extra = t - x14 - y14
    Rs = []
    for a in depth2.grid(min(extra, C['E']), s1):
        for b in depth2.grid(min(extra - a, C['F']), s1):
            c = extra - a - b
            if -EPS <= c <= C['G'] + EPS: Rs.append((x14, y14, a, b, max(0.0, c)))
    print('class A: x=%g y=%g z=0+ t=%g (units k/14); %d first requests; K grid %g; R2 grid %g' % (x14, y14, t, len(Rs), s1, h), flush=True)
    t0 = time.time(); res = []
    with Pool(NP) as p:
        for (R, e, v) in p.imap_unordered(work, [(C, R, t, s1, h) for R in Rs]):
            res.append((R, e, v))
            print('  R1 extra (E,F,G)=%s: %s' % (R[2:], 'SPOILED by K excl %s, depth-1 value %.4f > t' % ({c: e[c] for c in 'EFG'}, v) if e else 'NO SPOILER (candidate)'), flush=True)
    print('spoiled %d / %d  (%.0fs)' % (sum(1 for r in res if r[1]), len(res), time.time() - t0), flush=True)
