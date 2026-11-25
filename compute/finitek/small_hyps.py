"""Arithmetic of the finite-k hypotheses for J' (Step 1), DS-b (strictness) and CORE 46 (o <= 4*omega-3)."""
import math

# ---- J' Step 1: two requests per round each of size <= T split a + b <= T between the two classes; a class member j has
# |I_j| <= k - (j-1)a  (a = points of I requested).  Fourth member misses I iff |I_3| = k-2a <= a  iff  k <= 3a.
# She needs this for both classes simultaneously: a = ceil(k/3) each, so 2*ceil(k/3) <= T.
bad = []
for k in range(1, 5001):
    T = math.ceil(3 * k / 4)
    if T < 2 * math.ceil(k / 3):
        bad.append(k)
print("J': k<=5000 with ceil(3k/4) < 2*ceil(k/3) (Step 1 would fail at the global minimum T):", bad)
# the continuum condition t>=2/3 corresponds to T >= 2k/3; the integer condition is T >= 2*ceil(k/3)
# exact check that Step-1 integer condition is equivalent to  3*floor(T/2) >= k  only when T even
print("J': T>=2*ceil(k/3) vs 3*floor(T/2)>=k differ at (k,T) with k<=60:",
      [(k, T) for k in range(1, 61) for T in range(1, 60) if (T >= 2 * math.ceil(k / 3)) != (3 * (T // 2) >= k)][:6], "...")

# ---- DS-b: forcing cost f = n-k+2d+1 ; centre part <= 5d ; request = max(f + 5d, 6d) = n-k+7d+1 (since n >= k-d).
viol = 0
for k in range(2, 200):
    for d in range(0, k // 8):
        for n in range(k - d, 2 * k):
            cost = max(n - k + 2 * d + 1 + 5 * d, 6 * d)
            assert cost == n - k + 7 * d + 1
print("DS-b: integer request cost = n-k+7d+1 identically (so the hypothesis is n-k+7d+1 <= T, i.e. strict)")

# ---- CORE 46: dichotomy, even k and odd k.  omega = c - T, c = n-k, o >= 2*omega, |U| = 2(c-o) >= 2*omega  (o <= T),
# g = n - o - |U| >= 0.  L-branch: kernel floor(n-3k/2) >= 2*omega.  H-branch: o <= 4*omega-3.
unc = both_gap = 0
mid = []
for k in range(4, 121):
    for T in range(math.ceil(3 * k / 4), k + 3):
        for n in range(k + T, 3 * k + 3):
            c = n - k
            om = c - T
            if om < 1:
                continue
            for o in range(2 * om, T + 1):
                U = 2 * (c - o)
                if n - o - U < 0:
                    continue
                L = ((2 * n - 3 * k) // 2) >= 2 * om
                H = o <= 4 * om - 3
                if not (L or H):
                    unc += 1
                if (not L) and (4 * om - 2 <= o <= 4 * om - 1):
                    mid.append((k, T, n, o))
print("46: instances where neither L nor H applies:", unc, "; instances with L false and o in {4w-2,4w-1} (where 'o<4w' would not suffice):", len(mid))
