from twin13_16a import balanced_requests
import itertools
for k in range(3, 9):
    w = -9; arg = None
    for p12 in range(k+1):
        for p13 in range(k+1-p12):
            for p23 in range(k+1):
                q1 = k-p12-p13; q2 = k-p12-p23; q3 = k-p13-p23
                if min(q1,q2,q3) < 0: continue
                pts = iter(range(1000))
                A12,A13,A23,Q1,Q2,Q3 = [[next(pts) for _ in range(s)] for s in (p12,p13,p23,q1,q2,q3)]
                a = [set(A12+A13+Q1), set(A12+A23+Q2), set(A13+A23+Q3)]
                if a[0] & a[1] & a[2]: continue
                U = len(set().union(*a))
                ml, _ = balanced_requests(a)
                ex = ml - U/2
                if ex > w: w, arg = ex, (p12,p13,p23,U,ml)
    print('k=%d max over equal-size anchors of (min-max load - |U|/2) = %.1f at (p12,p13,p23,|U|,load)=%s' % (k, w, arg))
