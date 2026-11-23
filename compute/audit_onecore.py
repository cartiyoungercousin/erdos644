"""Exhaustive integer audit of the proof of Lemma 4.1 (one surviving cell), Appendix A.

Parameters: k, T, cell sizes x,y,z of a good triple satisfying the nine hypotheses of Lemma 4.1.
Response K avoids X, Y and Z0 (|Z0| = min(z, T-x-y)). Its traces: q = |Z∩K|, a = |A| (F∩K minus
Q, inside P_F), b = |B| (G∩K minus Q, inside P_G), c = |C| = |E∩K| (inside P_E). Constraints:
  q <= z - z0, a <= k-x-z, b <= k-y-z, c <= k-x-y,
  q + a + x + z0 <= k   (F∩K = Q∪A avoids X ∪ Z0 inside F)
  q + b + y + z0 <= k   (G∩K = Q∪B avoids Y ∪ Z0 inside G)
  q + a + b + c <= k    (disjoint parts of K).
For each such tuple, follow the manuscript's case choice and check that the three bases have
size <= T and that D = P_E \\ K (size d = k-x-y-c) fits into the residual capacities.
"""
import itertools
import sys


def hyp(k, T, x, y, z):
    S = x + y + z
    return (T >= x + y and 2 * T >= k + 2 * x and 2 * T >= k + 2 * y and T >= k + x - y - z and
            T >= k - x + y - z and 3 * T >= 3 * k - S and 5 * T >= 3 * k + S and
            3 * T >= k + x + y + 2 * z and 4 * T >= 2 * k + 3 * z)


def check(k, T, x, y, z, q, a, b, c):
    d = k - x - y - c
    v = z - q
    if c <= T - z:                                   # Case 0
        sizes = [q + x + b, q + y + a, z + c]
        case = 0
    elif a < k + x + z - 2 * T:                      # Case 1
        cap2, cap3 = T - y - a - z, T - z
        if cap2 < 0 or c > cap2 + cap3:
            return False, "case1-split"
        c2 = min(c, cap2); c3 = c - c2
        sizes = [q + x + b, y + a + z + c2, z + c3]
        case = 1
    elif b < k + y + z - 2 * T:                      # Case 2 (mirror)
        cap2, cap3 = T - x - b - z, T - z
        if cap2 < 0 or c > cap2 + cap3:
            return False, "case2-split"
        c2 = min(c, cap2); c3 = c - c2
        sizes = [q + y + a, x + b + z + c2, z + c3]
        case = 2
    else:                                            # Case 3
        u = c + z - T
        if not (0 < u <= c):
            return False, "case3-u"
        lo = max(0, y + a + z + u - T)
        hi = min(v, T - q - x - b - u)
        if lo > hi:
            return False, "case3-theta"
        theta = lo
        sizes = [q + x + b + u + theta, q + y + a + u + (v - theta), z + (c - u)]
        case = 3
    if any(s > T for s in sizes):
        return False, f"case{case}-size {sizes}"
    if sum(sizes) + d > 3 * T:
        return False, f"case{case}-D total {sum(sizes) + d} > 3T"
    return True, case


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    n = bad = 0
    cases = [0, 0, 0, 0]
    for k in range(1, kmax + 1):
        for T in range(0, k + 1):
            for x, y, z in itertools.product(range(k + 1), repeat=3):
                if x + y > k or x + z > k or y + z > k or not hyp(k, T, x, y, z):
                    continue
                z0 = min(z, T - x - y)
                for q in range(0, z - z0 + 1):
                    for a in range(0, min(k - x - z, k - q - x - z0) + 1):
                        for b in range(0, min(k - y - z, k - q - y - z0) + 1):
                            for c in range(0, min(k - x - y, k - q - a - b) + 1):
                                n += 1
                                ok, info = check(k, T, x, y, z, q, a, b, c)
                                if ok:
                                    cases[info] += 1
                                else:
                                    bad += 1
                                    if bad <= 10:
                                        print("FAIL", dict(k=k, T=T, x=x, y=y, z=z, q=q, a=a, b=b, c=c), info)
    print(f"k <= {kmax}: {n} response configurations, failures {bad}, per-case counts {cases}")
