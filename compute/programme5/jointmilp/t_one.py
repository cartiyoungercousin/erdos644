import sys, time, jm
S = jm.sizes(6.75); t = 12 - 0.002
r1 = dict(zip(jm.C7, [float(x) for x in sys.argv[1].split(',')]))
m1, o1 = jm.oracle1(S, r1, jm.SPEC, wpad={'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3})
print('M1', {c: round(v, 3) for c, v in m1.items()}, 'o1', round(o1, 3))
t0 = time.time()
def log(s): print('%6.1fs' % (time.time() - t0), s, flush=True)
res = jm.stage2(S, m1, o1, t, jm.SPEC, maxit=100, log=log)
print(res[0], res[2])
