import time, jm
S = jm.sizes(6.75); t = 12 - 0.002
for name, spec in (('nospec', jm.NOSPEC), ('spec', jm.SPEC)):
    for r1 in ({'X': 6, 'Y': 5, 'A': .75, 'B': .248}, {'X': 2, 'Y': .73, 'A': 2, 'B': 7.25}, {'X': 6, 'A': 5.998}):
        t0 = time.time()
        o = jm.oracle1(S, r1, spec); m1, o1 = o
        res = jm.stage2(S, m1, o1, t, spec, maxit=60)
        print(name, r1, 'M1', {c: round(v, 3) for c, v in m1.items() if v > 1e-6}, 'o1 %.3f' % o1, '->', res[0], 'it', res[2], 'pats', len(res[1]) if res[0] != 'REQ' else res[1][2][0], '%.1fs' % (time.time() - t0), flush=True)
