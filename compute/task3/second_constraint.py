r"""Task 3(2): profile families with a SECOND independent constraint, scanned for tau - 3k/4 and tested for (7,2).
Families (edges = k-sets A; cells V = V_1 + ... + V_q, profile a_j = |A & V_j|):
  P2[R]  : q = 3 (X1, X2, Y),     (a_1 mod 2, a_2 mod 2) in R, R a subset of F_2^2  (two parity classes / products;
           R = {01, 10} is FKW on X1+X2, R = {11} is "both odd")
  P22[R] : q = 4 (X1, Y1, X2, Y2),(a_1 mod 2, a_3 mod 2) in R  (tensor of two FKW-type cells)
  M3[R]  : q = 2 (X, Y),          a_1 mod 3 in R, R a subset of Z_3
tau exactly by profiles [proved by hand: S is a transversal iff its complement contains no edge; membership depends on
the profile only, so tau = min |s| over profiles s with no allowed p <= v - s].  For tau >= 3k/4 + 2 the family is
tested for a good seven by the HiGHS MILP of compute/core12/profile_search.py (copied; seven slots + per-cell co-type
counts + up-set intersecting support).  A found seven is re-checked by plain code [computed exact]; "no seven" is
[solver-only].  Only k + T <= n <= 3k - T with T = ceil(3k/4 + 2) - 1.  Candidates are deduplicated by (cells, co-edge profile set);
a candidate containing all slot profiles of an already found seven on the same cells has that seven (monotonicity)
[computed exact, cut re-used].  Usage: py -3.14 second_constraint.py KMIN KMAX [P22_KMAX]"""
import sys, itertools, json, time, numpy as np
from math import ceil
from scipy.optimize import milp, LinearConstraint, Bounds
import os
OFFSET = float(os.environ.get("OFFSET", "2"))  # tau >= 3k/4 + OFFSET
COT = list(range(1, 128))
LINES = [0b0000111, 0b0011001, 0b1100001, 0b0101010, 0b1010010, 0b1001100, 0b0110100]
FANO_UP = [I for I in range(1, 128) if any(I & L == L for L in LINES)]
def fano_seven(Pl, cells):
    """Fast sufficient pass: support restricted to co-types containing a line of ONE fixed Fano plane (pairwise
    intersecting automatically, since two lines meet). No order constraints (slots are labelled by the plane)."""
    q = len(cells); m = len(Pl); L = len(FANO_UP); nA = 7 * m; nv = nA + q * L
    A_ = lambda i, r: i * m + r; Z_ = lambda j, t: nA + j * L + t
    rows, lo, hi = [], [], []
    def add(co, l, h):
        a = np.zeros(nv)
        for jj, v in co: a[jj] += v
        rows.append(a); lo.append(l); hi.append(h)
    for i in range(7): add([(A_(i, r), 1) for r in range(m)], 1, 1)
    for j in range(q):
        add([(Z_(j, t), 1) for t in range(L)], cells[j], cells[j])
        for i in range(7):
            add([(Z_(j, t), 1) for t, I in enumerate(FANO_UP) if I >> i & 1] + [(A_(i, r), -Pl[r][j]) for r in range(m)], 0, 0)
    ub = np.array([1] * nA + [cells[j] for j in range(q) for _ in range(L)], float)
    res = milp(c=np.zeros(nv), constraints=LinearConstraint(np.array(rows), lo, hi), integrality=np.ones(nv),
               bounds=Bounds(np.zeros(nv), ub), options={'time_limit': 60})
    if res.status != 0: return None
    x = np.round(res.x).astype(int)
    slots = [Pl[next(r for r in range(m) if x[A_(i, r)])] for i in range(7)]
    z = [{FANO_UP[t]: int(x[Z_(j, t)]) for t in range(L) if x[Z_(j, t)]} for j in range(q)]
    for j in range(q):
        assert sum(z[j].values()) == cells[j]
        for i in range(7): assert sum(v for I, v in z[j].items() if I >> i & 1) == slots[i][j]
    sup = set(I for zj in z for I in zj); assert all(a & b for a in sup for b in sup)
    return slots, z
def good_seven(Pl, cells):
    f = fano_seven(Pl, cells)
    if f is not None: return f
    return good_seven_full(Pl, cells)
def good_seven_full(Pl, cells):
    q = len(cells); m = len(Pl); nA = 7 * m; nZ = q * 127; nv = nA + nZ + 127
    A_ = lambda i, r: i * m + r; Z_ = lambda j, I: nA + j * 127 + I; U_ = lambda I: nA + nZ + I
    rows, lo, hi = [], [], []
    def add(co, l, h):
        a = np.zeros(nv)
        for jj, v in co: a[jj] += v
        rows.append(a); lo.append(l); hi.append(h)
    for i in range(7): add([(A_(i, r), 1) for r in range(m)], 1, 1)
    for i in range(6): add([(A_(i, r), r) for r in range(m)] + [(A_(i + 1, r), -r) for r in range(m)], -np.inf, 0)
    for j in range(q):
        add([(Z_(j, I), 1) for I in range(127)], cells[j], cells[j])
        for i in range(7):
            add([(Z_(j, I), 1) for I in range(127) if COT[I] >> i & 1] + [(A_(i, r), -Pl[r][j]) for r in range(m)], 0, 0)
        for I in range(127): add([(Z_(j, I), 1), (U_(I), -cells[j])], -np.inf, 0)
    for J in range(1, 127):
        if J < (127 ^ J): add([(U_(J - 1), 1), (U_((127 ^ J) - 1), 1)], 1, 1)
        for e in range(7):
            if not J >> e & 1: add([(U_(J - 1), 1), (U_((J | 1 << e) - 1), -1)], -np.inf, 0)
    ub = np.array([1] * nA + [cells[j] for j in range(q) for _ in range(127)] + [1] * 127, float)
    lb = np.zeros(nv); lb[U_(126)] = 1
    res = milp(c=np.zeros(nv), constraints=LinearConstraint(np.array(rows), lo, hi), integrality=np.ones(nv),
               bounds=Bounds(lb, ub), options={'time_limit': 600})
    if res.status == 2: return None
    if res.status != 0: return 'TIMEOUT'
    x = np.round(res.x).astype(int)
    slots = [Pl[next(r for r in range(m) if x[A_(i, r)])] for i in range(7)]
    z = [{COT[I]: int(x[Z_(j, I)]) for I in range(127) if x[Z_(j, I)]} for j in range(q)]
    for j in range(q):  # plain re-check
        assert sum(z[j].values()) == cells[j]
        for i in range(7): assert sum(v for I, v in z[j].items() if I >> i & 1) == slots[i][j]
    sup = set(I for zj in z for I in zj); assert all(a & b for a in sup for b in sup)
    return slots, z
def boxes(cells, total):
    out = []
    def rec(j, left, cur):
        if j == len(cells) - 1:
            if left <= cells[j]: out.append(tuple(cur + [left]))
            return
        for a in range(min(left, cells[j]) + 1): rec(j + 1, left - a, cur + [a])
    rec(0, total, []); return out
def tau(cells, E):
    best = None
    for t in range(sum(cells) + 1):
        for s in boxes(cells, t):
            comp = [v - a for v, a in zip(cells, s)]
            if not any(all(p[j] <= comp[j] for j in range(len(cells))) for p in E): return t
    return None
kmin, kmax = int(sys.argv[1]), int(sys.argv[2]); P22MAX = int(sys.argv[3]) if len(sys.argv) > 3 else 0
NLIST = [int(v) for v in sys.argv[4].split(',')] if len(sys.argv) > 4 else None
subsets = lambda U: [R for r in range(1, len(U)) for R in itertools.combinations(U, r)]
F22 = [(0, 0), (0, 1), (1, 0), (1, 1)]
best = {}; cands = []
for k in range(kmin, kmax + 1):
    target = ceil(3 * k / 4 + OFFSET)
    T_ = target - 1
    for n in (NLIST or range(k + T_, 3 * k - T_ + 1)):   # confined range k + T <= n <= 3k - T (outside it: TWIN reductions / Theorem A side)
        fams = []
        for n1 in range(1, n):
            fams += [('M3', R, (n1, n - n1)) for R in subsets([0, 1, 2])]
            for n2 in range(1, n - n1):
                if n2 > n1: continue
                fams += [('P2', R, (n1, n2, n - n1 - n2)) for R in subsets(F22)]
                if n - n1 - n2 >= 2 and k <= P22MAX:
                    for y1 in range(1, n - n1 - n2):
                        fams += [('P22', R, (n1, y1, n2, n - n1 - n2 - y1)) for R in subsets(F22)]
        for kind, R, cells in fams:
            if kind == 'M3': E = [p for p in boxes(cells, k) if p[0] % 3 in R]
            elif kind == 'P2': E = [p for p in boxes(cells, k) if (p[0] % 2, p[1] % 2) in R]
            else: E = [p for p in boxes(cells, k) if (p[0] % 2, p[2] % 2) in R]
            if not E: continue
            # antichain/nondegeneracy: drop families where some cell lies in every edge (then tau <= that cell... kept)
            t = tau(cells, E)
            if t is None: continue
            key = (k, kind); best[key] = max(best.get(key, (-1,)), (t, n, R, cells))
            if t >= target: cands.append((k, n, kind, R, cells, t, E))
for key in sorted(best): print("best tau", key, "->", best[key][0], "(3k/4 =", 3 * key[0] / 4, ") at n, R, cells =", best[key][1:], flush=True)
print("candidates with tau >= 3k/4 + 2:", len(cands), flush=True)
out = open(f"logs/second_constraint_off{OFFSET:g}_{kmin}_{kmax}{'_n' + sys.argv[4].replace(',', '-') if NLIST else ''}.jsonl", "w")
cands.sort(key=lambda c: (c[0], c[1], c[4], len(c[6])))
seen = {}; cuts = {}; stat = {}
for (k, n, kind, R, cells, t, E) in cands:
    t0 = time.time(); Pl = sorted(tuple(v - a for v, a in zip(cells, p)) for p in E); key = (cells, tuple(Pl))
    if key in seen: stat['dup'] = stat.get('dup', 0) + 1; continue
    seen[key] = 1; PS = set(Pl)
    if any(c_ <= PS for c_ in cuts.get(cells, [])): stat['cut'] = stat.get('cut', 0) + 1; continue
    gs = good_seven(Pl, list(cells)); dt = time.time() - t0
    if isinstance(gs, tuple): cuts.setdefault(cells, []).append(set(map(tuple, gs[0])))
    stat[str(gs is None)] = stat.get(str(gs is None), 0) + 1
    if sum(stat.values()) % 200 == 0: print("progress", stat, flush=True)
    st = 'NO_SEVEN[solver-only]' if gs is None else ('TIMEOUT' if gs == 'TIMEOUT' else 'GOOD_SEVEN[exact]')
    print(f"k={k} n={n} {kind} R={R} cells={cells} tau={t} (3k/4+{t-3*k/4}): {st} {dt:.1f}s", flush=True)
    out.write(json.dumps({'k': k, 'n': n, 'kind': kind, 'R': R, 'cells': cells, 'tau': t, 'status': st,
                          'seven': None if not isinstance(gs, tuple) else {'slots': gs[0], 'z': [{str(a): b for a, b in zj.items()} for zj in gs[1]]}}) + "\n"); out.flush()
print("summary: dup / covered-by-earlier-seven / MILP found seven (False) / MILP no seven (True):", stat, flush=True)
