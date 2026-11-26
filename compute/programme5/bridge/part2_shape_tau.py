"""Exact tau of the FULL shape family H_J (all k-sets of V = R1|R2|P whose profile (r1,r2,p) is in J),
via the profile criterion tau(H_J) > T iff every u (sum T, 0<=u<=a) has some j in J with j <= a-u.
Any explicit family of that shape is a subfamily, so tau(H_J) is an exact UPPER bound for it. [computed exact]
Usage: py part2_shape_tau.py k  (scans partitions with n in a window)"""
import sys, itertools
from part2_lib import record
k = int(sys.argv[1]); g = round(k / 7); rr = lambda x: int(round(x))
def types(w):
    return {"C1": ((k - g, k), (0, g), (0, g)), "C2": ((0, g), (k - g, k), (0, g)),
            "E": ((rr(3*k/7) - w, rr(3*k/7) + w), (rr(5*k/14) - w, rr(5*k/14) + w), (rr(3*k/14) - w, k)),
            "K": ((rr(k/2) - w, rr(k/2) + w), (rr(k/2) - w, rr(k/2) + w), (0, 2 * w))}
def J_of(a, b, p, TY, use):
    J = []
    for r1 in range(min(a, k) + 1):
        for r2 in range(min(b, k - r1) + 1):
            q = k - r1 - r2
            if q > p: continue
            for t in use:
                (l1, h1), (l2, h2), (l3, h3) = TY[t]
                if l1 <= r1 <= h1 and l2 <= r2 <= h2 and l3 <= q <= h3: J.append((r1, r2, q)); break
    return J
def tau_J(a, b, p, J):
    for T in range(a + b + p + 1):
        for u1 in range(min(a, T) + 1):
            for u2 in range(min(b, T - u1) + 1):
                u3 = T - u1 - u2
                if u3 > p: continue
                if not any(j[0] <= a - u1 and j[1] <= b - u2 and j[2] <= p - u3 for j in J): return T
    return None
print(f"k={k} record={record(k)}")
for w in (1, 2):
    TY = types(w)
    for use in (("C1", "C2", "E", "K"), ("C1", "C2", "E"), ("C1", "C2", "K")):
        best = None
        for n in range(round(1.75 * k), round(2.5 * k) + 1):
            for p in range(0, n // 3 + 1):
                for a in range(k - g, n - p - (k - g) + 1):
                    b = n - p - a
                    if b < a: continue
                    J = J_of(a, b, p, TY, use)
                    if not J: continue
                    t = tau_J(a, b, p, J)
                    if best is None or t > best[0]: best = (t, (a, b, p))
                    if n == round(31 * k / 14) and (a, b, p) in ((k, k, n - 2 * k), (k + 1, k + 1, n - 2 * k - 2)):
                        print(f"  w={w} types={'+'.join(use)} (|R1|,|R2|,|P|)={(a,b,p)} n={n}: tau(full shape)={t}")
        print(f"w={w} types={'+'.join(use)}: max tau(full shape) over n in [1.75k,2.5k] = {best[0]} at {best[1]}")
