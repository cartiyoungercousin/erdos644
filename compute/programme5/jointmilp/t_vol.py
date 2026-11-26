import jm, sys, time
S = jm.sizes(7.0); T = 11.998
r1 = dict(zip(jm.C7, [float(x) for x in sys.argv[1].split(',')]))
WS = [None, {'X': 1, 'Y': 1, 'A': 1.3, 'B': 1.3}, {'X': 1.3, 'Y': 1.3, 'A': 1, 'B': 1}, {'X': 1, 'Y': 1.3, 'A': 1.3, 'B': 1}, {'X': 1.3, 'Y': 1, 'A': 1, 'B': 1.3}]
for om in (0, 1.0, 1.25, 1.5, 2.0, 3.0):
    for w in WS:
        o = jm.oracle1(S, r1, jm.SPEC, w=w, wpad={'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3}, extra=lambda m, mm, oo: m.row(oo, om))
        if o is None: print(om, 'none'); continue
        m1, o1 = o; t0 = time.time()
        res = jm.stage2(S, m1, o1, T, jm.SPEC, maxit=120, tl=150)
        print('o1>=%.2f w=%s M1=%s o1=%.3f -> %s it %d %.1fs' % (om, w and list(w.values()), [round(m1[c], 3) for c in jm.C7], o1, res[0], res[2], time.time() - t0), (res[1][2][0] if res[0] == 'REQ' else ''), flush=True)
        if res[0] == 'ADV': sys.exit()
