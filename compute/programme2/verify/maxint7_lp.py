"""Exact LP value for each of the 716 S_7-classes of maximal intersecting families M on [7].

Pattern model (CORE 1.3/8.3/16): co-types F in M with masses m_F >= 0, every member of mass 1:
  sum_{F not containing i} m_F >= 1 (i = 1..7),   N = sum m_F,   minimise N.
inf N over patterns with support inside M equals LP(M) (support may be enlarged by an arbitrarily small mass).
A pattern is Fano-type iff its support lies in one of the 30 Fano up-sets; these are maximal, so a pattern
is NON-Fano iff its support is not contained in any Fano up-set iff it extends to a maximal M that is not a
Fano up-set. Hence:  [N < 11/6 => Fano-type]  <=>  LP(M) >= 11/6 for every non-Fano maximal M.

Each LP value is certified EXACTLY: rational primal m and rational dual w, both checked feasible in
Fractions, with equal objectives.  Dual: max sum w_i s.t. sum_{i not in F} w_i <= 1 for F in M.
"""
import json, sys, itertools
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog

FULL = 127

def parse(hx):
    v = int(hx, 16)
    return [g for g in range(128) if v >> g & 1]

def minimal(M):
    S = set(M)
    return [F for F in M if not any((F & ~(1 << i)) in S for i in range(7) if F >> i & 1)]

def fano_upsets():
    base = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]
    seen = set()
    for p in itertools.permutations(range(7)):
        lines = frozenset(sum(1 << p[a] for a in l) for l in base)
        seen.add(lines)
    ups = set()
    for lines in seen:
        ups.add(frozenset(g for g in range(128) if any(g & l == l for l in lines)))
    assert len(ups) == 30
    return ups

def ratio(x, den=5040):
    return Fr(x).limit_denominator(den)

def exact_lp(M):
    Fs = minimal(M)
    # primal: min sum m_F, A m >= 1 where A[i][F] = 1 if i not in F
    A = np.array([[0 if F >> i & 1 else 1 for F in Fs] for i in range(7)], dtype=float)
    if (A.sum(axis=1) == 0).any():
        return None, None, None  # infeasible: some point in every co-type (then that member is empty)
    r = linprog(np.ones(len(Fs)), A_ub=-A, b_ub=-np.ones(7), bounds=[(0, None)] * len(Fs), method='highs')
    assert r.status == 0
    m = [ratio(x) for x in r.x]
    # dual
    rd = linprog(-np.ones(7), A_ub=A.T, b_ub=np.ones(len(Fs)), bounds=[(0, None)] * 7, method='highs')
    assert rd.status == 0
    w = [ratio(x) for x in rd.x]
    # exact checks
    for i in range(7):
        if sum(m[j] for j, F in enumerate(Fs) if not F >> i & 1) < 1:
            return 'primal-fail', m, w
    for F in M:  # all members, not only minimal ones
        if sum(w[i] for i in range(7) if not F >> i & 1) > 1:
            return 'dual-fail', m, w
    if any(x < 0 for x in m) or any(x < 0 for x in w):
        return 'sign-fail', m, w
    P, D = sum(m), sum(w)
    if P != D:
        return 'gap', m, w
    return P, dict((Fs[j], m[j]) for j in range(len(Fs)) if m[j]), w

def main(path):
    ups = fano_upsets()
    rows = [json.loads(l) for l in open(path)]
    res = []
    for r in rows:
        M = parse(r['mask'])
        fano = any(frozenset(M) == u for u in ups)
        val, m, w = exact_lp(M)
        if isinstance(val, str):
            print('CERT FAILURE', val, r['mask']); sys.exit(1)
        res.append((val, fano, r, m, w))
    inf = [x for x in res if x[0] is None]
    fin = sorted([x for x in res if x[0] is not None], key=lambda x: x[0])
    print('classes', len(res), 'infeasible (dictator-like)', len(inf), 'Fano classes', sum(x[1] for x in res))
    print('labelled families covered', sum(x[2]['count'] for x in res))
    nonfano = [x for x in fin if not x[1]]
    print('Fano LP values', sorted(set(str(x[0]) for x in fin if x[1])))
    print('smallest LP values over NON-Fano classes:')
    for val, fano, r, m, w in nonfano[:8]:
        print(' ', val, float(val), 'aut', r['aut'], 'support', {format(F, '07b')[::-1]: str(x) for F, x in m.items()},
              'dual w', [str(x) for x in w])
    below = [x for x in nonfano if x[0] < Fr(11, 6)]
    print('NON-Fano classes with LP < 11/6:', len(below))
    json.dump([{'mask': x[2]['mask'], 'lp': str(x[0]), 'fano': x[1],
                'primal': {str(F): str(v) for F, v in (x[3] or {}).items()},
                'dual': [str(v) for v in (x[4] or [])]} for x in res],
              open(path.replace('.jsonl', '_lp.json'), 'w'))

if __name__ == '__main__':
    main(sys.argv[1])
