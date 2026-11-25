r"""Exact SAT check (python-sat, CaDiCaL): does H = (a+C) cap (V choose k) contain seven DISTINCT members
with no transversal of size <= 2?  mode 'fano': Fano-type (pencil triples empty) w.r.t. some labelling
(WLOG fixed labelling, since the sets are unlabelled); mode 'any': arbitrary good seven."""
import itertools
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from core import PENCIL, popc, verify_seven

def good_seven_sat(cs, k, mode='any'):
    n = cs.n; pool = IDPool(); cl = []
    b = lambda i, x: pool.id(('b', i, x))
    for i in range(7):
        cl += CardEnc.equals([b(i, x) for x in range(n)], k, vpool=pool, encoding=EncType.seqcounter).clauses
        for j, h in enumerate(cs.H):
            xs = [x for x in range(n) if h >> x & 1]; want = cs.alpha >> j & 1
            # Tseitin chain: c_t = c_{t-1} xor b_t
            prev = None
            for x in xs:
                v = b(i, x)
                if prev is None: prev = v; continue
                c = pool.id(('x', i, j, x))
                cl += [[-c, prev, v], [-c, -prev, -v], [c, -prev, v], [c, prev, -v]]
                prev = c
            if prev is None:
                if want: return 'UNSAT', None
            else: cl.append([prev] if want else [-prev])
    if mode == 'fano':
        for p in range(7):
            i, j, l = PENCIL[p]
            for x in range(n): cl.append([-b(i, x), -b(j, x), -b(l, x)])
    else:
        for x in range(n):
            for y in range(x, n):
                avs = []
                for i in range(7):
                    a = pool.id(('av', i, x, y)); avs.append(a)
                    cl += [[-a, -b(i, x)], [-a, -b(i, y)]]
                cl.append(avs)
    # distinctness: sets i<j differ somewhere
    for i in range(7):
        for j in range(i + 1, 7):
            ds = []
            for x in range(n):
                d = pool.id(('d', i, j, x)); ds.append(d)
                cl += [[-d, b(i, x)], [-d, -b(j, x)]]
            cl.append(ds)
    with Solver(name='cd19', bootstrap_with=cl) as s:
        if not s.solve(): return 'UNSAT', None
        mdl = set(v for v in s.get_model() if v > 0)
        B = [sum(1 << x for x in range(n) if b(i, x) in mdl) for i in range(7)]
        ok, why = verify_seven(cs, k, B, require_fano=(mode == 'fano'))
        assert ok, why
        return 'SAT', B
