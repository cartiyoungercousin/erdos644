import sys, time, numpy as np, fast2
k = 14.0
d = float(sys.argv[1]); al = float(sys.argv[2]); h = float(sys.argv[3]); be = float(sys.argv[4]) if len(sys.argv) > 4 else 14 - al
t = (12 - d) / k
types = {3: 6/k, 5: 5/k, 6: 0.0, 12: al/k, 4: (9-al)/k, 10: be/k, 2: max(0,8-be)/k, 9: 0.0, 1: 3/k}
P = fast2.Pos4(types)
t0 = time.time()
v, R, L = fast2.depth1x(P, t, h/k)
print('delta=%g t=%.4f alpha=%g beta=%g: depth-1 value x14 = %.4f  R=%s L=%s  %.1fs' % (d, t, al, be, v*k, np.round(R*k,3), np.round(L*k,3), time.time()-t0), flush=True)
