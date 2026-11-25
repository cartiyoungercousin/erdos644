r"""CORE 112: exact search for T-covering co-edge families with NO good seven inside the class of PROFILE families of a
fixed partition V = V_1 u ... u V_q (|V_j| = n_j): the family is a union of whole profile classes
C(p) = {K : |K cap V_j| = p_j}, sum p_j = c = n - k.  Every Sym(V_1) x ... x Sym(V_q)-invariant family is of this form
(e.g. the FKW parity family: q = 2, p_X odd).
 - T-covering  <=>  every T-profile s (sum s = T, s <= n) is dominated by a chosen p  (hand: a T-set of profile s lies in
   some K of profile p iff s <= p, and C(p) is the whole class).
 - Good seven  <=>  slots p^1..p^7 in P and co-type counts z_{j,I} >= 0 (I subset [7] nonempty) with sum_I z_{j,I} = n_j,
   sum_{I ni i} z_{j,I} = p^i_j, support pairwise intersecting  (hand: realise by placing points cellwise).
SAT (Glucose4, with DRUP proof) on profile variables b_p with covering clauses (+ optional nondegeneracy: every cell
has a point avoided by some member); lazy cut  not(b_{p^1} and ... and b_{p^7})  for each good seven found (MILP, HiGHS),
after greedily shrinking the SAT model to a minimal covering subfamily.  Every cut's good seven is re-checked by plain
code and logged; on UNSAT the CNF and a DRUP proof are written for check_drup.py.  Each good seven is also scanned for
(Sigma)-shapes among its sub-triples / sub-quadruples (finite-k forms).
Usage: py -3.14 profile_search.py k T n n_1,n_2,...,n_q [nondeg|x] [tag]"""
import sys, itertools, json, time, numpy as np
from fractions import Fraction as F
from scipy.optimize import milp, LinearConstraint, Bounds
from pysat.solvers import Glucose4

k, T, n = map(int, sys.argv[1:4]); cells = list(map(int, sys.argv[4].split(','))); q = len(cells)
nondeg = len(sys.argv) > 5 and sys.argv[5] == 'nondeg'; tag = sys.argv[6] if len(sys.argv) > 6 else 'run'
assert sum(cells) == n; c = n - k


def boxes(total):
    out = []
    def rec(j, left, cur):
        if j == q - 1:
            if left <= cells[j]: out.append(tuple(cur + [left]))
            return
        for a in range(min(left, cells[j]) + 1): rec(j + 1, left - a, cur + [a])
    rec(0, total, []); return out


P = boxes(c); S = boxes(T); idx = {p: i + 1 for i, p in enumerate(P)}
dom = lambda p, s: all(a >= b for a, b in zip(p, s))
clauses = [[idx[p] for p in P if dom(p, s)] for s in S]
if nondeg:
    for j in range(q): clauses.append([idx[p] for p in P if p[j] < cells[j]])
COT = list(range(1, 128)); DISJ = [(a, b) for a, b in itertools.combinations(range(127), 2) if COT[a] & COT[b] == 0]


def good_seven(Pset):
    Pl = sorted(Pset); m = len(Pl); nA = 7 * m; nZ = q * 127; nv = nA + nZ + 127
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
    # support inside a maximal intersecting family: an up-set containing exactly one of J, [7]-J (implies intersecting)
    for J in range(1, 127):
        if J < (127 ^ J): add([(U_(J - 1), 1), (U_((127 ^ J) - 1), 1)], 1, 1)
        for e in range(7):
            if not J >> e & 1: add([(U_(J - 1), 1), (U_((J | 1 << e) - 1), -1)], -np.inf, 0)
    ub = np.array([1] * nA + [cells[j] for j in range(q) for _ in range(127)] + [1] * 127, float)
    lb = np.zeros(nv); lb[U_(126)] = 1  # [7] itself is in every maximal intersecting family
    res = milp(c=np.zeros(nv), constraints=LinearConstraint(np.array(rows), lo, hi), integrality=np.ones(nv),
               bounds=Bounds(lb, ub), options={'time_limit': 900})
    if res.status == 2: return None
    if res.status != 0: raise RuntimeError(f'MILP status {res.status} {res.message}')
    x = np.round(res.x).astype(int)
    slots = [Pl[next(r for r in range(m) if x[A_(i, r)])] for i in range(7)]
    z = [{COT[I]: int(x[Z_(j, I)]) for I in range(127) if x[Z_(j, I)]} for j in range(q)]
    return slots, z


def check_seven(slots, z, Pset):  # plain re-check, no solver
    assert all(s_ in Pset for s_ in slots)
    for j in range(q):
        assert sum(z[j].values()) == cells[j]
        for i in range(7): assert sum(v for I, v in z[j].items() if I >> i & 1) == slots[i][j]
    sup = set(I for zj in z for I in zj)
    assert all(a & b for a in sup for b in sup) and 0 not in sup
    return True


def sigma_shapes(z):
    tot = {}
    for zj in z:
        for I, v in zj.items(): tot[I] = tot.get(I, 0) + v
    found = []
    for tr in itertools.combinations(range(7), 3):
        reg = {}
        for I, v in tot.items():
            r = sum(1 << a for a, i in enumerate(tr) if I >> i & 1); reg[r] = reg.get(r, 0) + v
        g = lambda r: reg.get(r, 0)
        kap = g(7); pa = [g(3) + kap, g(5) + kap, g(6) + kap]
        if g(0) == 0 and kap >= n - 2 * T: found.append(('pencil', tr))
        if kap == 0 and max(pa) <= F(T + n - 2 * k, 2) and sum(pa) >= F(3 * n - 3 * k - T, 2): found.append(('T', tr))
    for qd in itertools.combinations(range(7), 4):
        reg = {}
        for I, v in tot.items():
            r = sum(1 << a for a, i in enumerate(qd) if I >> i & 1); reg[r] = reg.get(r, 0) + v
        g = lambda r: reg.get(r, 0)
        sig = sum(g(r) for r in range(16) if bin(r).count('1') <= 1)
        if 2 * sig <= 3 * T - n and all(g(a) + g(b) + sig <= T for a, b in [(3, 12), (5, 10), (9, 6)]):
            found.append(("Q'", qd))
    return found


def ok(PS):
    return all(any(dom(p, s_) for p in PS) for s_ in S) and \
        (not nondeg or all(any(p[j] < cells[j] for p in PS) for j in range(q)))


t0 = time.time(); s = Glucose4(bootstrap_with=clauses, with_proof=True); log = []
it = 0; result = None; fam = None
while True:
    it += 1
    if not s.solve(): result = 'UNSAT'; break
    model = set(v for v in s.get_model() if v > 0); cur = [p for p in P if idx[p] in model]
    for p in list(cur):
        trial = [x for x in cur if x != p]
        if ok(trial): cur = trial
    gs = good_seven(cur)
    if gs is None: result = 'FOUND'; fam = cur; break
    slots, z = gs; check_seven(slots, z, set(cur))
    shp = sigma_shapes(z)
    cut = [-idx[p] for p in sorted(set(slots))]; s.add_clause(cut); clauses.append(cut)
    log.append({'family': [list(p) for p in cur], 'slots': slots, 'z': [{str(I): v for I, v in zj.items()} for zj in z], 'shapes': [[a, list(b)] for a, b in shp]})
    if time.time() - t0 > 2400: result = 'TIMEOUT'; break
el = time.time() - t0
noshape = sum(1 for e in log if not e['shapes'])
print(f"k={k} T={T} n={n} cells={cells} nondeg={nondeg}: {result} after {it} SAT calls, {len(log)} cuts, {el:.1f}s; "
      f"|profiles|={len(P)}; good sevens without any (Sigma)-shape: {noshape}/{len(log)}", flush=True)
base = f"logs/prof_{tag}_{k}_{T}_{n}_{'-'.join(map(str, cells))}{'_nd' if nondeg else ''}"
json.dump({'k': k, 'T': T, 'n': n, 'cells': cells, 'nondeg': nondeg, 'result': result, 'sevens': log}, open(base + '.json', 'w'))
if result == 'UNSAT':
    with open(base + '.cnf', 'w') as f:
        f.write(f"p cnf {len(P)} {len(clauses)}\n" + "".join(" ".join(map(str, cl)) + " 0\n" for cl in clauses))
    with open(base + '.drup', 'w') as f: f.write("\n".join(s.get_proof()) + "\n")
if result == 'FOUND':
    print("  FAMILY (profiles):", fam)
    json.dump({'cells': cells, 'k': k, 'T': T, 'n': n, 'profiles': [list(p) for p in fam]}, open(base + '_family.json', 'w'))
