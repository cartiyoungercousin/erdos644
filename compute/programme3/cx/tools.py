"""Shared tools for Programme 3 counterexample search (cx).
Families are lists of python-int bitmasks on n <= 64 points.
- tau_ilp: exact transversal number (HiGHS MIP).
- seven_sat: is there a good seven (7 members, no 2-point transversal)? General type, not only Fano.
- triple_stats: W = min |x1^x2^x3| over all member triples (repeats allowed), P = min over pencil triples.
Lemma Q (PROGRAMME3_CX.md): if W > (12n - 21k)/7 then H has no Fano-type good seven.
"""
import numpy as np

POP16 = np.array([bin(i).count('1') for i in range(1 << 16)], dtype=np.int64)

def popcount64(a):
    a = np.asarray(a, dtype=np.uint64)
    c = np.zeros(a.shape, dtype=np.int64)
    for s in range(0, 64, 16):
        c += POP16[((a >> np.uint64(s)) & np.uint64(0xFFFF)).astype(np.int64)]
    return c

def _highs_cover(fam, n, integer, timelimit):
    import highspy
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    h.setOptionValue('time_limit', float(timelimit))
    inf = highspy.kHighsInf
    for _ in range(n):
        h.addVar(0, 1)
    idx = np.arange(n, dtype=np.int32)
    h.changeColsCost(n, idx, np.ones(n))
    if integer:
        h.changeColsIntegrality(n, idx, np.array([highspy.HighsVarType.kInteger] * n))
    for B in fam:
        r = np.array([i for i in range(n) if B >> i & 1], dtype=np.int32)
        h.addRow(1, inf, len(r), r, np.ones(len(r)))
    h.run()
    info = h.getInfo()
    return info, h.modelStatusToString(h.getModelStatus())

def tau_ilp(fam, n, timelimit=300):
    info, st = _highs_cover(fam, n, True, timelimit)
    return int(round(info.objective_function_value)), float(info.mip_dual_bound), st

def tau_lp(fam, n):
    info, st = _highs_cover(fam, n, False, 300)
    return float(info.objective_function_value)

def triple_stats(fam, maxpairs=2_000_000, seed=0):
    """Exact if M(M-1)/2 <= maxpairs, else random pairs (third member always scanned exhaustively)."""
    A = np.array(fam, dtype=np.uint64); M = len(A)
    W = int(popcount64(A).min()); P = 10 ** 9
    exact = M * (M - 1) // 2 <= maxpairs
    if exact:
        I, J = np.triu_indices(M, 1)
    else:
        rng = np.random.default_rng(seed)
        I = rng.integers(0, M, maxpairs); J = rng.integers(0, M, maxpairs)
        k = I != J; I, J = I[k], J[k]
    step = max(1, 4_000_000 // M)
    for s in range(0, len(I), step):
        a, b = A[I[s:s + step]], A[J[s:s + step]]
        D = popcount64((a ^ b)[:, None] ^ A[None, :])
        W = min(W, int(D.min()))
        pen = ((a & b)[:, None] & A[None, :]) == 0
        if pen.any():
            P = min(P, int(D[pen].min()))
    return W, P, exact

def seven_sat(fam, n, conf_budget=3_000_000, first=None):
    """General good-seven search: 7 members whose complements cover every pair (and every point).
    first: index of a member forced into slot 0 (valid for vertex... member-transitive families)."""
    from pysat.solvers import Cadical153
    M = len(fam); nv = [0]
    def new():
        nv[0] += 1; return nv[0]
    s = [[new() for _ in range(M)] for _ in range(7)]
    m = [[new() for _ in range(n)] for _ in range(7)]
    S = Cadical153()
    for i in range(7):
        S.add_clause(s[i][:])
        for b, B in enumerate(fam):
            for x in range(n):
                if B >> x & 1:
                    S.add_clause([-s[i][b], m[i][x]])
    if first is not None:
        S.add_clause([s[0][first]])
    for x in range(n):
        for y in range(x, n):
            ps = []
            for i in range(7):
                p = new(); ps.append(p)
                S.add_clause([-p, -m[i][x]])
                if y != x:
                    S.add_clause([-p, -m[i][y]])
            S.add_clause(ps)
    S.conf_budget(conf_budget)
    r = S.solve_limited()
    if r is True:
        mod = set(v for v in S.get_model() if v > 0)
        return 'SEVEN', [fam[next(b for b in range(M) if s[i][b] in mod)] for i in range(7)]
    return ('NONE', None) if r is False else ('UNKNOWN', None)

def check_seven(seven, n):
    for x in range(n):
        for y in range(x, n):
            t = (1 << x) | (1 << y)
            if all(B & t for B in seven):
                return False
    return True
