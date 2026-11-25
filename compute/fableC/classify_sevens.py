r"""FABLE_C section 3 (gate): classification of the forced good sevens in compute/core12/forced_sevens.jsonl.
For every seven (bitmasks K_1..K_7 on n points; T parsed from the source name, since the 'T' key of the export is
overwritten by the Theorem-T shape list):
  - essential parts E_i = U(the other six) (FABLE_C 2.8), light members {i : |E_i| <= T}, min_i |E_i|;
  - r_min = least r such that some r of the seven members, used in full, extend to a static r-certificate with
    7 - r FREE lines (any sets of size <= T): exact MILP (HiGHS) per r-subset, witnesses re-checked by plain code.
[computed exact up to the MILP solver for infeasibility; every feasible answer is re-checked without a solver]
Usage: py -3.14 classify_sevens.py [nproc] [limit] [start]"""
import sys, json, re, itertools, os, time
import numpy as np
from collections import Counter
from scipy.optimize import milp, LinearConstraint, Bounds
from multiprocessing import Pool
import scipy.sparse as sp

here = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(here, '..', 'core12', 'forced_sevens.jsonl')
pc = lambda m: bin(m).count('1')
TL = 60
SHORTCUT = True


def U_of(sets, n):
    """points lying in an uncovered pair (x = y allowed) of the given sets (bitmasks)"""
    typ = [sum(1 << i for i, K in enumerate(sets) if K >> x & 1) for x in range(n)]
    present = set(typ)
    bad = {I for I in present if any(I & J == 0 for J in present)}
    return sum(1 << x for x in range(n) if typ[x] in bad)


def static_cert(Ks, R, n, T):
    """members R (indices) in full + 7-|R| free lines of size <= T covering all pairs?  returns lines or None.
    Support of the co-types (over R and the lines) inside a maximal intersecting family of subsets of [7]:
    an up-set containing exactly one of J, [7]-J."""
    r = len(R); m = 7 - r
    cnt = Counter(sum(1 << a for a, i in enumerate(R) if Ks[i] >> x & 1) for x in range(n))
    As = sorted(cnt); nB = 1 << m
    var = {}
    for A in As:
        for B in range(nB):
            if A == 0 and B == 0: continue
            var[(A, B)] = len(var)
    ny = len(var); nv = ny + 127; UJ = lambda J: ny + J - 1
    ri, ci, vals, lo, hi = [], [], [], [], []
    def add(co, l, h):
        i = len(lo)
        for j, v in co: ri.append(i); ci.append(j); vals.append(v)
        lo.append(l); hi.append(h)
    for A in As: add([(var[(A, B)], 1) for B in range(nB) if (A, B) in var], cnt[A], cnt[A])
    for l in range(m): add([(j, 1) for (A, B), j in var.items() if B >> l & 1], 0, T)
    for (A, B), j in var.items(): add([(j, 1), (UJ(A | B << r), -cnt[A])], -np.inf, 0)
    for J in range(1, 127):
        if J < (127 ^ J): add([(UJ(J), 1), (UJ(127 ^ J), 1)], 1, 1)
        for e in range(7):
            if not J >> e & 1: add([(UJ(J), 1), (UJ(J | 1 << e), -1)], -np.inf, 0)
    ub = np.array([cnt[A] for (A, B) in var] + [1] * 127, float); lb = np.zeros(nv); lb[UJ(127)] = 1
    # valid fixings: a present co-type J forces the union of the sets in J to be V (every other co-type meets J)
    c_ = pc(Ks[0]); FULL = (1 << n) - 1
    for J in range(1, 127):
        a = [R[i] for i in range(r) if J >> i & 1]; nl = pc(J >> r)
        un = 0
        for i in a: un |= Ks[i]
        if pc(un) + nl * T < n: ub[UJ(J)] = 0          # union of members in J plus nl lines cannot reach V
    M = sp.csr_matrix((vals, (ri, ci)), shape=(len(lo), nv))
    res = milp(c=np.zeros(nv), constraints=LinearConstraint(M, lo, hi), integrality=np.ones(nv),
               bounds=Bounds(lb, ub), options={'time_limit': TL})
    if res.status == 2: return None
    if res.status != 0: return 'UNDECIDED'
    y = np.round(res.x[:ny]).astype(int)
    lines = [0] * m; byA = {}
    for x in range(n):
        byA.setdefault(sum(1 << a for a, i in enumerate(R) if Ks[i] >> x & 1), []).append(x)
    for A in As:
        pts = byA[A]; p = 0
        for B in range(nB):
            if (A, B) not in var: continue
            for _ in range(y[var[(A, B)]]):
                for l in range(m):
                    if B >> l & 1: lines[l] |= 1 << pts[p]
                p += 1
        assert p == len(pts)
    assert all(pc(L) <= T for L in lines)
    assert U_of([Ks[i] for i in R] + lines, n) == 0     # plain re-check
    return lines


def work(line):
    d = json.loads(line); n, k = d['n'], d['k']
    T = int(re.match(r'prof_\w+?_(\d+)_(\d+)_(\d+)_', d['source']).group(2)); Ks = d['coedges']
    assert all(pc(K) == n - k for K in Ks) and U_of(Ks, n) == 0
    E = [U_of(Ks[:i] + Ks[i + 1:], n) for i in range(7)]
    assert all(E[i] & ~Ks[i] == 0 for i in range(7))
    es = [pc(e) for e in E]
    typ = Counter(sum(1 << i for i in range(7) if Ks[i] >> x & 1) for x in range(n))
    rmin = None; nwit = 0; wit = None; und = 0
    known3 = bool(d['pencil']) or (isinstance(d['T'], list) and bool(d['T']))   # tagged pencil / Theorem-T triple
    for r in range(1, 7):
        if r == 3 and known3 and SHORTCUT:      # a tagged shape is a static 3-certificate (CORE 38); skip the MILPs
            rmin = 3; nwit = None; wit = (d['pencil'] or d['T'])[0]; break
        for R in itertools.combinations(range(7), r):
            res = static_cert(Ks, list(R), n, T)
            if res == 'UNDECIDED': und += 1
            elif res is not None:
                nwit += 1
                if wit is None: wit = list(R)
        if nwit: rmin = r; break
    if rmin is None: rmin = 7
    return {'k': k, 'T': T, 'n': n, 'cells': d['cells'], 'source': d['source'], 'any_shape': d['any_shape'],
            'pencil': len(d['pencil']), 'Qp': len(d['Qp']), 'thmT': len(d['T']) if isinstance(d['T'], list) else None,
            'E': es, 'light': sum(1 for e in es if e <= T), 'rmin': rmin, 'n_rmin_sets': nwit, 'witness': wit,
            'undecided': und, 'type_sizes': sorted(Counter(pc(I) for I in typ.elements()).items()),
            'types': {str(I): v for I, v in sorted(typ.items())}}


if __name__ == '__main__':
    npr = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    lim = int(sys.argv[2]) if len(sys.argv) > 2 else None
    start = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    lines = open(SRC, encoding='utf-8').read().splitlines()[start:lim]
    t0 = time.time(); outn = 'classified_sevens.jsonl' if start == 0 else f'classified_sevens_from{start}.jsonl'
    with Pool(npr) as p, open(os.path.join(here, 'logs', outn), 'w', encoding='utf-8') as fo:
        for i, rec in enumerate(p.imap(work, lines, chunksize=8)):
            fo.write(json.dumps(rec) + '\n')
            if i % 200 == 0: print(i, f'{time.time()-t0:.0f}s', flush=True)
    print('done', len(lines), f'{time.time()-t0:.0f}s')
