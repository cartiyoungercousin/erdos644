"""Exhaustive integer audit of the case analyses in six_sevenths_v3.tex.

For every k in a range and T = ceil(6k/7), enumerate all cell-size tuples allowed by each
proposition and check that the lemma the manuscript invokes in that case really has all its
(integer) hypotheses satisfied. This checks the *case logic*, not the lemmas themselves.
Any failure is a gap in the manuscript (or a transcription error here) and gets investigated.
"""
import sys
from math import ceil, floor


def pos(v):
    return max(0, v)

# ---------------- lemma hypotheses (manuscript §3–§4), exact integer forms -------------
def hall_cor(k, T, a, b, c):        # Cor 3.2: a <= T/2, b,c <= T - k/2, b+c <= 3T-2k
    return 6 * k <= 7 * T and 2 * a <= T and k + 2 * b <= 2 * T and k + 2 * c <= 2 * T and b + c <= 3 * T - 2 * k


def symmetric(k, T, m, y, z):        # Lemma 3.4, needs m >= y >= z
    S = m + y + z
    return m >= y >= z and T >= k + m - y - z and 2 * T >= k + m and 3 * T >= 2 * k + m + y - z and 5 * T >= 3 * k + S


def onecore(k, T, x, y, z):          # Lemma 4.1
    S = x + y + z
    return (T >= x + y and 2 * T >= k + 2 * x and 2 * T >= k + 2 * y and T >= k + x - y - z and
            T >= k - x + y - z and 3 * T >= 3 * k - S and 5 * T >= 3 * k + S and
            3 * T >= k + x + y + 2 * z and 4 * T >= 2 * k + 3 * z)


def splitA(k, T, x, y, z):           # Lemma 4.2
    S = x + y + z
    return T >= S and 2 * T >= k + 2 * y and 2 * T >= k + 2 * x - y + z and 3 * T >= k + 2 * x + y + 3 * z


def splitB(k, T, x, y, z):           # Lemma 4.3
    S = x + y + z
    return T >= S and 3 * T >= k + 3 * x and T >= k - x + z and 3 * T >= k + 2 * x + 3 * y + z


def gaptraces(k, T, x, y, z, l, u):  # Lemma 4.4
    S = x + y + z
    p, t = pos(k - x - y - u), pos(k - x - z - u)
    return S + p + t <= T and k + 3 * x + p + t <= 3 * T and y + z + 2 * l <= T


def gapcore(k, T, x, y, z, l, u):    # Lemma 4.5
    S = x + y + z
    D = pos(S - T)
    return (x + y <= T and k - x - y <= u and k - x - z + D <= u and 2 * x + 2 * D + k - y - z <= 2 * T
            and y + z + 2 * l <= T and 2 * k + x - y + l + D <= 3 * T)


def twocores(k, T, x, y, z, l, u):   # Lemma 4.6
    S = x + y + z
    g = pos(k - y - u)
    return (g <= min(x, z) and y + 2 * g <= T and x + l <= T and z + l <= T and k + 2 * y <= 2 * T
            and 3 * k <= 4 * T and 3 * k + S <= 5 * T)


def nearcore(k, T, x, y, z, m):      # Lemma 4.7 (dichotomy with threshold m, 2m <= k)
    S = x + y + z
    D = pos(S - T)
    common = (2 * m <= k and y + z <= T and m + z <= T and x + m <= T and k + y - z <= T and
              2 * k + x - 2 * z <= 2 * T and 2 * k + x + m - z <= 3 * T)
    alt1 = (k - x + y + D <= T and 2 * k - 2 * x + z + D <= 2 * T and 2 * k - z + D <= 2 * T and
            3 * k - x - y + D <= 3 * T)
    alt2 = S <= T and k - x + y <= T and 2 * k - 2 * x + z <= 2 * T
    return common and (alt1 or alt2)


fails = []


def fail(*msg):
    fails.append(msg)
    if len(fails) <= 20:
        print("FAIL", *msg)


# ---------------- Proposition 5.1 (local finisher) ------------------------------------------
def prop_local_finish(k, T):
    h = k - T
    gamma = T - ceil(k / 2)
    for M in range(0, T // 2 + 1):
        if 2 * M > k:
            continue
        for y in range(0, M + 1):
            for z in range(0, y + 1):
                if M + y > k or M + z > k or y + z > k:
                    continue
                two_medium = y > gamma >= z
                if not two_medium and y + z <= 3 * T - 2 * k:
                    ok = hall_cor(k, T, M, y, z)
                    case = 1
                elif not two_medium:
                    ok = symmetric(k, T, M, y, z)
                    case = 2
                elif z > h:
                    # twocores with (x,y,z) := (M, z, y), Gap(M, floor(k/2))
                    ok = twocores(k, T, M, z, y, M, k // 2)
                    case = 3
                else:
                    ok = nearcore(k, T, M, z, y, M)
                    case = 4
                if not ok:
                    fail("Prop5.1", dict(k=k, T=T, M=M, y=y, z=z, case=case))


# ---------------- Lemma 6.1 + Props 6.2–6.4 (three gaps) ------------------------------------
def endpoints(k):
    h, s = k // 7, k % 7
    T = k - h
    alpha = T // 2
    beta = (4 * T - 2 * k) // 3
    gamma = T - ceil(k / 2)
    delta = 2 * k - T - 2 * beta
    lam = delta - 1
    return h, s, T, alpha, beta, gamma, delta, lam


def check_endpoints(k):
    h, s, T, alpha, beta, gamma, delta, lam = endpoints(k)
    r = (h + 2 * s) // 3
    assert alpha == 3 * h + s // 2 and beta == 3 * h + r and gamma == (5 * h + s) // 2
    assert delta == 2 * h + s - 2 * r and lam == 2 * h + s - 2 * r - 1
    conds = [0 <= gamma <= alpha <= beta, beta >= 3 * h, lam <= gamma - h, 4 * lam <= T,
             k - beta - 1 + lam <= T]
    if not all(conds):
        fail("Lemma6.1", k, conds)
    if beta < k // 2:
        if not (h < delta <= gamma and 0 <= lam < gamma < k and T + beta - k <= gamma - 1):
            fail("Lemma6.1-branch", k)


def prop_gap_one(k):
    h, s, T, alpha, beta, gamma, delta, lam = endpoints(k)
    for q in range(alpha + 1, min(beta, k // 2) + 1):
        # capped request with cap gamma: precondition
        if not (gamma <= k - q and 0 <= 2 * k - T - q <= 2 * gamma):
            fail("Prop6.2-cap", k, q)
        x = q
        for y in range(0, gamma + 1):
            for z in range(0, y + 1):
                if x + y > k or x + z > k or y + z > k:
                    continue
                d, v = y - z, y + z
                if d > x - h:
                    ok, case = splitA(k, T, x, y, z), 1
                elif v <= 3 * T - k - 2 * x:
                    ok, case = onecore(k, T, y, z, x), 2
                else:
                    ok, case = symmetric(k, T, x, y, z), 3
                if not ok:
                    fail("Prop6.2", dict(k=k, q=q, y=y, z=z, case=case))


def prop_gap_two(k):
    h, s, T, alpha, beta, gamma, delta, lam = endpoints(k)
    if not beta < k // 2:
        return
    for q in range(delta, gamma + 1):
        if not (beta <= k - q and 0 <= 2 * k - T - q <= 2 * beta):
            fail("Prop6.3-cap", k, q)
        x = q
        for y in range(0, alpha + 1):
            for z in range(0, y + 1):
                if x + y > k or x + z > k or y + z > k:
                    continue
                if x + z <= k - beta - 1:
                    ok, case = hall_cor(k, T, y, x, z), 1
                else:
                    ok, case = twocores(k, T, y, x, z, alpha, beta), 2
                if not ok:
                    fail("Prop6.3", dict(k=k, q=q, y=y, z=z, case=case))


def prop_gap_three(k):
    h, s, T, alpha, beta, gamma, delta, lam = endpoints(k)
    if not beta < k // 2:
        return
    J = 2 * k - gamma + 2 * (k // 2) - 3 * T
    if J != (h - s) // 2:
        fail("Prop6.4-J", k, J, (h - s) // 2)
    for q in range(beta + 1, k // 2 + 1):
        if not (gamma <= k - q and 0 <= 2 * k - T - q <= 2 * gamma):
            fail("Prop6.4-cap", k, q)
        x = q
        for y in range(0, lam + 1):
            for z in range(0, y + 1):
                if x + y > k or x + z > k or y + z > k:
                    continue
                S = x + y + z
                if S <= T and (S <= 2 * T - k or z < J):
                    ok, case = splitB(k, T, x, z, y), 1
                elif 2 * T - k < S <= T and z >= J:
                    ok, case = gaptraces(k, T, x, y, z, lam, gamma), 2
                else:
                    ok, case = gapcore(k, T, x, y, z, lam, gamma), 3
                if not ok:
                    fail("Prop6.4", dict(k=k, q=q, y=y, z=z, case=case))


if __name__ == "__main__":
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    for k in range(7, kmax + 1):
        T = ceil(6 * k / 7)
        assert T == k - k // 7
        prop_local_finish(k, T)
        check_endpoints(k)
        prop_gap_one(k)
        prop_gap_two(k)
        prop_gap_three(k)
    print(f"k = 7..{kmax}: total failures = {len(fails)}")
