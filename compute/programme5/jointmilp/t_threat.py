"""Threat line R1 = Y u B' (|B'| = t-5): his answers M1 = X(6-d) u A(7) u B_eps u outside(1-delta+d), and variants."""
import jm, time, sys, json, multiprocessing as mp
S = jm.sizes(7.0); T = 11.998; dl = 0.002
C = []
for d in (0.0, 0.1, 0.2, 0.25, 0.3, 0.5, 1.0):
    C.append((6 - d, 0, 7, dl, 0, 0, 0, 1 - dl + d))               # drop d of X
for d in (0.25, 0.5):
    C.append((6, 0, 7 - d, dl, 0, 0, 0, 1 - dl + d))               # drop d of A
C.append((5.75, 0, 7, dl, 0, 1.0, 0, 0.248))                        # X drop, Fd pad
C.append((5.75, 0, 7, 0, 0, 0, 0, 1.25))                            # X drop, B_eps dropped too
C.append((5.5, 0, 6.75, dl, 0, 0, 0, 1.748))
def work(st):
    m1 = dict(zip(jm.C7, st[:7])); t0 = time.time()
    if not all(jm.in_spec(sum(m1[c] for c in cs), jm.SPEC) for cs in jm.MEM.values()): return st, 'ILLEGAL', 0, 0, None
    res, info, it, _ = jm.stage2(S, m1, st[7], T, jm.SPEC, maxit=150, tl=150)
    return st, res, it, round(time.time() - t0, 1), ([{('%s%d' % k): round(v, 4) for k, v in info[0].items() if v > 1e-7}, round(info[1], 4), round(info[2][0], 4)] if res == 'REQ' else None)
if __name__ == '__main__':
    with mp.Pool(12) as p:
        for out in p.imap_unordered(work, C): print(out, flush=True)
