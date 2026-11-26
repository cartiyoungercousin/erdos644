import jm, time
S = jm.sizes(7.0)
for t in (11.998, 12.0, 12.05):
  for r in ([6, 5, 1, 0, 0, 0, 0], [6, 5, .998, 0, 0, 0, 0], [6, 0, 6, 0, 0, 0, 0], [2, 1, 2, 7, 0, 0, 0]):
    r1 = dict(zip(jm.C7, r)); r1['A'] = min(r1['A'], 7); s = t - sum(r) 
    if s > 0: r1['B'] += s
    m1, o1 = jm.oracle1(S, r1, jm.NOSPEC)
    t0 = time.time(); res = jm.stage2(S, m1, o1, t, jm.NOSPEC, maxit=60)
    print('t=%g' % t, {c: round(v, 3) for c, v in r1.items() if v}, res[0], res[2], '%.1fs' % (time.time() - t0), flush=True)
