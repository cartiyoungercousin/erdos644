import jm, time
S = jm.sizes(7.0); T = 11.998
st = [6.0, 0.0, 6.75, 0.002, 0.0, 0.0, 0.0, 1.248]
m1 = dict(zip(jm.C7, st[:7])); t0 = time.time()
def log(s): print('%5.0fs' % (time.time() - t0), s, flush=True)
orig = jm.oracle2
def o2(*a, **k):
    r = orig(*a, **k)
    if r is not None and k.get('margin', 0) == 0 and 'engine_first' not in k:
        log('    M2: %s  |U|=%.4f' % ({'%s%d' % kk: round(v, 3) for kk, v in r[1].items() if v > 1e-6}, r[0]))
    return r
jm.oracle2 = o2
res = jm.stage2(S, m1, st[7], T, jm.SPEC, maxit=40, tl=60, log=log, wall=150)
print(res[0], res[2])
