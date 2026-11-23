"""Exhaustively validate explicit split formulas for the Hall allocation (manuscript Lemma 3.1).

Bins (requests) 1..4 have capacities c1=T-a, c2=T-a-b, c3=T-a-c, c4=T-b-c after placing the
pair cells. Private parts: P_E (size pe = k-a-b) -> bins {3,4}; P_F (pf = k-a-c) -> {2,4};
P_G (pg = k-b-c) -> {1,2,3}. Check: whenever the 11 inequalities hold, the formulas below give a
valid nonnegative split. Also check the 11 inequalities are exactly Hall's conditions (so the
lemma is sharp), by brute-force feasibility.
"""
import itertools


def formulas(k, T, a, b, c):
    pe, pf, pg = k - a - b, k - a - c, k - b - c
    c1, c2, c3, c4 = T - a, T - a - b, T - a - c, T - b - c
    g1 = min(pg, c1)
    q = pg - g1
    x = min(pe, c3)            # P_E into bin 3 (as much as possible)
    y = min(pf, c2)            # P_F into bin 2
    d = max(0, q - (c2 - y) - (c3 - x))   # deficit for the rest of P_G
    de = min(d, x)             # move this much of P_E from bin 3 to bin 4
    df = d - de                # and this much of P_F from bin 2 to bin 4
    x2, y2 = x - de, y - df
    z = min(q, c2 - y2)        # rest of P_G into bin 2, remainder into bin 3
    g2, g3 = z, q - z
    e3, e4, f2, f4 = x2, pe - x2, y2, pf - y2
    return dict(g1=g1, g2=g2, g3=g3, f2=f2, f4=f4, e3=e3, e4=e4, pe=pe, pf=pf, pg=pg)


def ok(k, T, a, b, c, w):
    if any(v < 0 for v in w.values()):
        return False
    return (w["g1"] + w["g2"] + w["g3"] == w["pg"] and w["f2"] + w["f4"] == w["pf"]
            and w["e3"] + w["e4"] == w["pe"] and a + w["g1"] <= T
            and a + b + w["f2"] + w["g2"] <= T and a + c + w["e3"] + w["g3"] <= T
            and b + c + w["e4"] + w["f4"] <= T)


def hyps(k, T, a, b, c):
    return (a + b <= k and a + c <= k and b + c <= k and
            a <= T and a + b <= T and a + c <= T and b + c <= T and
            k + 2 * b <= 2 * T and k + 2 * c <= 2 * T and k + 3 * a <= 3 * T and
            2 * k + b + c <= 3 * T and 2 * k + 2 * a + b <= 4 * T and
            2 * k + 2 * a + c <= 4 * T and 3 * k + a <= 4 * T)


def feasible_bruteforce(k, T, a, b, c):
    pe, pf, pg = k - a - b, k - a - c, k - b - c
    for g1 in range(pg + 1):
        for g2 in range(pg - g1 + 1):
            g3 = pg - g1 - g2
            for f2 in range(pf + 1):
                for e3 in range(pe + 1):
                    w = dict(g1=g1, g2=g2, g3=g3, f2=f2, f4=pf - f2, e3=e3, e4=pe - e3,
                             pe=pe, pf=pf, pg=pg)
                    if ok(k, T, a, b, c, w):
                        return True
    return False


if __name__ == "__main__":
    bad = 0
    count = 0
    for k in range(0, 16):
        for T in range(0, k + 3):
            for a, b, c in itertools.product(range(k + 1), repeat=3):
                if hyps(k, T, a, b, c):
                    count += 1
                    if not ok(k, T, a, b, c, formulas(k, T, a, b, c)):
                        bad += 1
                        if bad <= 5:
                            print("FORMULA FAILS", k, T, a, b, c, formulas(k, T, a, b, c))
    print(f"checked {count} parameter tuples satisfying the 11 inequalities; formula failures: {bad}")
    # sharpness: inequalities <=> feasibility (small k, brute force)
    mism = 0
    for k in range(0, 9):
        for T in range(0, k + 2):
            for a, b, c in itertools.product(range(k + 1), repeat=3):
                if a + b <= k and a + c <= k and b + c <= k and a + b <= T and a + c <= T and b + c <= T:
                    if hyps(k, T, a, b, c) != feasible_bruteforce(k, T, a, b, c):
                        mism += 1
    print("hypotheses == brute-force feasibility (k<=8), mismatches:", mism)
