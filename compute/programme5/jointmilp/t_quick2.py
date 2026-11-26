import time, jm, sys
S = jm.sizes(6.75); t = 12 - 0.002
pool = []
for r in ([4.248, 0, 3, 3, 1, .75, 0], [6, 5, .75, .248, 0, 0, 0], [2, .73, 2, 7.25, 0, 0, 0], [4.0, 1.0, 0.248, 5.0, 1.0, 0.75, 0.0], [2.0, 5.0, 4.0, 0.248, 0.0, 0.75, 0.0]):
    r1 = dict(zip(jm.C7, r)); m1, o1 = jm.oracle1(S, r1, jm.SPEC, wpad={'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3})
    for P in ([], pool):
        t0 = time.time(); res = jm.stage2(S, m1, o1, t, jm.SPEC, maxit=100, pool=P)
        print(r, res[0], 'it', res[2], 'pool', len(P), '%.1fs' % (time.time() - t0), flush=True)
    pool = (pool + res[3])[-30:]
