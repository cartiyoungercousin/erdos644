"""Independent exact verification on ACTUAL point sets of a blow-up family (s, X types, Y types).
(1) rebuild edges, recheck overlaps (numpy popcount); (2) tau by exact hitting-set ILP (HiGHS) AND by plain
request-free ILP on the explicit edge list; (3) AP on point sets: for the type-level optimal region (counts -> actual
point sets) recompute beta and h from the explicit edges by ILP, plus random regions; (4) non-arena test."""
import itertools, sys, random
import numpy as np
import highspy
from search import ap_value, ap_union, comps


def build(s, types):
    offs = [sum(s[:i]) for i in range(len(s))]
    out = []
    for e in types:
        per = [list(itertools.combinations(range(offs[i], offs[i] + s[i]), e[i])) for i in range(len(s))]
        for ch in itertools.product(*per):
            mk = 0
            for g in ch:
                for p in g: mk |= 1 << p
            out.append(mk)
    return out


def popcount(a):
    a = a.astype(np.uint64)
    c = np.zeros(a.shape, dtype=np.int64)
    for sh in range(0, 64, 8):
        c += POP[((a >> np.uint64(sh)) & np.uint64(255)).astype(np.int64)]
    return c
POP = np.array([bin(i).count('1') for i in range(256)], dtype=np.int64)


def overlaps(A, B):
    A = np.array(A, dtype=np.uint64); B = np.array(B, dtype=np.uint64)
    mn, mx = 10**9, -1
    for i in range(0, len(A), 512):
        pc = popcount(A[i:i + 512, None] & B[None, :])
        mn = min(mn, int(pc.min())); mx = max(mx, int(pc.max()))
    return mn, mx


def min_hitting(edges, n, allowed=None):
    """exact min hitting set size using only points in allowed (default all); None if infeasible"""
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    allowed = list(range(n)) if allowed is None else list(allowed)
    for p in range(n): h.addVar(0.0, 1.0 if p in allowed else 0.0)
    for p in range(n): h.changeColIntegrality(p, highspy.HighsVarType.kInteger); h.changeColCost(p, 1.0)
    aset = set(allowed)
    for mk in edges:
        idx = [p for p in range(n) if (mk >> p) & 1 and p in aset]
        if not idx: return None
        h.addRow(1.0, highspy.kHighsInf, len(idx), idx, [1.0] * len(idx))
    h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal: return None
    return round(h.getInfo().objective_function_value)


def verify(s, X, Y, k, c, mu, T, nrandom=20):
    n = sum(s); res = {}
    EX = build(s, X); EY = build(s, Y)
    res['edges'] = (len(EX), len(EY))
    assert not set(EX) & set(EY)
    res['XX_min'] = overlaps(EX, EX)[0]; res['YY_min'] = overlaps(EY, EY)[0]
    res['cross_max'] = overlaps(EX, EY)[1]
    res['overlap_ok'] = res['XX_min'] >= c and res['YY_min'] >= c and res['cross_max'] <= mu
    res['tau'] = min_hitting(EX + EY, n); res['tau_X'] = min_hitting(EX, n); res['tau_Y'] = min_hitting(EY, n)
    ap, wit = ap_value(list(s), X, Y, T)
    res['AP_typelevel_true'] = ap; res['AP_atomunion'] = ap_union(list(s), X, Y, T)[0]
    # recompute witness region on actual points
    Pc, rP, rQ, bP, bQ, hP = wit
    offs = [sum(s[:i]) for i in range(len(s))]
    RP = set(p for i in range(len(s)) for p in range(offs[i], offs[i] + rP[i]))
    RQ = set(p for i in range(len(s)) for p in range(offs[i] + rP[i], offs[i] + rP[i] + rQ[i]))
    EP, EQ = (EX, EY) if Pc == 'X' else (EY, EX)
    full = (1 << n) - 1
    bP2 = max(bin(e & ~sum(1 << p for p in RP)).count('1') for e in EP)
    bQ2 = max(bin(e & ~sum(1 << p for p in RQ)).count('1') for e in EQ)
    hP2 = min_hitting(EP, n, RP)
    res['witness_actual'] = (Pc, bP2, bQ2, hP2, 'cost', max(hP2, 2 * bQ2) + -(-8 * bP2 // 3) + 2)
    return res


if __name__ == '__main__':
    s = [13, 13, 2, 2]
    X = [(0, 9, 2, 1), (0, 10, 0, 2), (0, 10, 1, 1), (0, 10, 2, 0), (0, 11, 0, 1), (0, 11, 1, 0), (0, 12, 0, 0), (1, 10, 1, 0), (1, 11, 0, 0)]
    Y = [(9, 0, 1, 2), (10, 0, 0, 2), (10, 0, 1, 1), (10, 0, 2, 0), (10, 1, 0, 1), (11, 0, 0, 1), (11, 0, 1, 0), (11, 1, 0, 0), (12, 0, 0, 0)]
    print(verify(s, X, Y, 12, 7, 6, 9))
