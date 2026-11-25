r"""CORE 114: does a T-covering PROFILE family contain a (Sigma)-shape?  Finite-k forms:
 (b) pencil:  3 members, union V, triple intersection >= n - 2T;
 (c) Thm T:   3 members, empty triple intersection, pair intersections <= (T+n-2k)/2, their sum >= (3n-3k-T)/2;
 (a) Q':      4 members, 2σ <= 3T - n, and for each matching (pair-only mass of the matching) + σ <= T.
Exact model: slots p^1..p^q from the family (q = 3 or 4), Venn counts z_{j,r} >= 0 per cell (r ⊆ slots),
sum_r z_{j,r} = n_j, sum_{r ∋ i} z_{j,r} = p^i_j.  MILP (HiGHS) [solver-only]; witnesses are re-checked by plain code.
Reads the families logged by profile_search.py (every candidate family = a minimal T-covering subfamily of a SAT model).
Usage: py -3.14 sigma_profile.py logs/prof_*.json ..."""
import sys, json, glob, numpy as np
from fractions import Fraction as F
from scipy.optimize import milp, LinearConstraint, Bounds


def shape_milp(cells, Pl, k, T, n, kind):
    q = len(cells); s = 3 if kind in ('pencil', 'T') else 4; R = 1 << s; m = len(Pl)
    nA = s * m; nv = nA + q * R
    A_ = lambda i, r: i * m + r; Z_ = lambda j, r: nA + j * R + r
    rows, lo, hi = [], [], []
    def add(co, l, h):
        a = np.zeros(nv)
        for jj, v in co: a[jj] += v
        rows.append(a); lo.append(l); hi.append(h)
    for i in range(s): add([(A_(i, r), 1) for r in range(m)], 1, 1)
    for i in range(s - 1): add([(A_(i, r), r) for r in range(m)] + [(A_(i + 1, r), -r) for r in range(m)], -np.inf, 0)
    for j in range(q):
        add([(Z_(j, r), 1) for r in range(R)], cells[j], cells[j])
        for i in range(s):
            add([(Z_(j, r), 1) for r in range(R) if r >> i & 1] + [(A_(i, t), -Pl[t][j]) for t in range(m)], 0, 0)
    tot = lambda rs: [(Z_(j, r), 1) for j in range(q) for r in rs]
    if kind == 'pencil':
        add(tot([0]), 0, 0); add(tot([7]), n - 2 * T, np.inf)
    elif kind == 'T':
        add(tot([7]), 0, 0); amax = (T + n - 2 * k) // 2
        for r in (3, 5, 6): add(tot([r]), -np.inf, amax)
        add(tot([3, 5, 6]), -((-(3 * n - 3 * k - T)) // 2), np.inf)
    else:
        sig = [r for r in range(16) if bin(r).count('1') <= 1]
        add(tot(sig), -np.inf, (3 * T - n) // 2)
        for a, b in [(3, 12), (5, 10), (9, 6)]: add(tot([a, b] + sig), -np.inf, T)
    ub = np.array([1] * nA + [cells[j] for j in range(q) for _ in range(R)], float)
    res = milp(c=np.zeros(nv), constraints=LinearConstraint(np.array(rows), lo, hi), integrality=np.ones(nv),
               bounds=Bounds(np.zeros(nv), ub), options={'time_limit': 600})
    if res.status == 2: return None
    if res.status != 0: return 'UNDECIDED'
    x = np.round(res.x).astype(int)
    slots = [Pl[next(t for t in range(m) if x[A_(i, t)])] for i in range(s)]
    z = [[int(x[Z_(j, r)]) for r in range(R)] for j in range(q)]
    # plain re-check
    for j in range(q):
        assert sum(z[j]) == cells[j]
        for i in range(s): assert sum(z[j][r] for r in range(R) if r >> i & 1) == slots[i][j]
    g = lambda r: sum(z[j][r] for j in range(q))
    if kind == 'pencil': assert g(0) == 0 and g(7) >= n - 2 * T
    elif kind == 'T': assert g(7) == 0 and max(g(3), g(5), g(6)) <= F(T + n - 2 * k, 2) and g(3) + g(5) + g(6) >= F(3 * n - 3 * k - T, 2)
    else:
        sg = sum(g(r) for r in range(16) if bin(r).count('1') <= 1)
        assert 2 * sg <= 3 * T - n and all(g(a) + g(b) + sg <= T for a, b in [(3, 12), (5, 10), (9, 6)])
    return slots


if __name__ == '__main__':
    files = [f for a in sys.argv[1:] for f in glob.glob(a)]
    nfam = 0; noshape = []; undec = 0; tally = {'pencil': 0, 'T': 0, "Q'": 0}
    for f in files:
        d = json.load(open(f, encoding='utf-8'))
        if d['result'] != 'UNSAT': continue
        for e in d['sevens']:
            if 'family' not in e: continue
            Pl = sorted(tuple(p) for p in e['family']); nfam += 1; got = []
            for kind in ('pencil', 'T', "Q'"):
                r = shape_milp(d['cells'], Pl, d['k'], d['T'], d['n'], kind)
                if r == 'UNDECIDED': undec += 1
                elif r is not None: got.append(kind); tally[kind] += 1
            if not got: noshape.append((d['k'], d['T'], d['n'], d['cells'], Pl))
    print(f"{nfam} candidate T-covering families checked; containing pencil {tally['pencil']}, Thm-T {tally['T']}, Q' {tally[chr(39) * 0 + 'Q' + chr(39)]}; "
          f"undecided MILPs {undec}; families with NO (Sigma)-shape: {len(noshape)}")
    for x in noshape: print("  NO SHAPE:", x)
