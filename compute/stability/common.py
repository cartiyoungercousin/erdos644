r"""Shared tools for the stability experiment (STABILITY_DATA.md).
Families are k-uniform sets stored as int64 bitmasks on n points.
(7,2) property: every 7 members have a 2-point transversal.  Equivalent exact form: H is NOT (7,2) iff some 7 members
have complements covering every pair of the n points (a pair {u,v} is a transversal of the seven iff no member avoids both).
So  (7,2)  <=>  minimum number of members whose complements cover all pairs is >= 8.   Checked by SAT (CaDiCaL) with a
cardinality bound, and independently by a HiGHS set-cover ILP.
tau: HiGHS ILP (min z(V), z(B)>=1), cross-checked by a bitset enumeration when n <= 22.
"""
import os, sys, json, itertools, random, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'programme2', 'task4'))
from gf2 import reduced_basis, annihilator, fwht, pc
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix

OUT = os.path.join(HERE, 'out'); FAM = os.path.join(HERE, 'fam')

def pairs(n): return [(i, j) for i in range(n) for j in range(i + 1, n)]

def _cover_lists(M, n, prs):
    """for each pair (i,j): indices of members whose complement contains both i and j."""
    bit = [((M >> i) & 1) == 0 for i in range(n)]
    return [np.flatnonzero(bit[i] & bit[j]) for (i, j) in prs]

def find_cover(M, n, bound, forced=None, solver='cadical153', seed=None):
    """Return list of <= bound member indices whose complements cover all pairs (plus the complement of `forced`, an
    extra mask, if given: forced counts toward the 7).  None if no such cover exists (UNSAT = exact certificate)."""
    M = np.asarray(M, dtype=np.int64); prs = pairs(n); full = (1 << n) - 1
    need = []
    for (i, j) in prs:
        if forced is not None and ((forced >> i) & 1) == 0 and ((forced >> j) & 1) == 0: continue
        need.append((i, j))
    if not need: return []
    cl = _cover_lists(M, n, need)
    if any(len(c) == 0 for c in cl): return None
    used = np.unique(np.concatenate(cl)); idx = {int(m): t + 1 for t, m in enumerate(used)}
    nv = len(used); clauses = [[idx[int(m)] for m in c] for c in cl]
    if bound >= nv: return [int(m) for m in used] if True else None
    card = CardEnc.atmost(lits=list(range(1, nv + 1)), bound=bound, top_id=nv, encoding=EncType.seqcounter)
    with Solver(name=solver, bootstrap_with=clauses + card.clauses) as s:
        if seed is not None:
            try: s.set_phases([(-1 if random.Random(seed + v).random() < 0.8 else 1) * v for v in range(1, nv + 1)])
            except Exception: pass
        if not s.solve(): return None
        model = s.get_model()
    return [int(used[v - 1]) for v in range(1, nv + 1) if model[v - 1] > 0]

def is_72(M, n, solver='cadical153'):
    """exact: True iff no 7 members cover all pairs by complements."""
    return find_cover(M, n, 7, None, solver) is None

def can_add(M, n, s):
    """H is (7,2) already.  Is H + {s} (7,2)?  Bad seven must contain s: 6 others cover the pairs not inside comp(s)."""
    return find_cover(M, n, 6, forced=s) is None

def bad_seven_with(M, n, s):
    return find_cover(M, n, 6, forced=s)

def is_72_ilp(M, n, tl=600):
    """independent exact check: min set cover of all pairs by complements >= 8 (HiGHS)."""
    M = np.asarray(M, dtype=np.int64); prs = pairs(n); cl = _cover_lists(M, n, prs)
    if any(len(c) == 0 for c in cl): return True, None, []
    rows = np.concatenate([np.full(len(c), r) for r, c in enumerate(cl)]); cols = np.concatenate(cl)
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(prs), len(M)))
    r = milp(c=np.ones(len(M)), constraints=LinearConstraint(A, 1, np.inf), integrality=np.ones(len(M)),
             bounds=Bounds(0, 1), options={'time_limit': tl})
    if r.status != 0: return None, None, []
    v = int(round(r.fun)); cover = [int(i) for i in np.flatnonzero(r.x > 0.5)]
    return v >= 8, v, cover

def tau_ilp(M, n, tl=600):
    M = np.asarray(M, dtype=np.int64)
    rows, cols = [], []
    for v in range(n):
        r = np.flatnonzero((M >> v) & 1); rows.append(r); cols.append(np.full(len(r), v))
    rows = np.concatenate(rows); cols = np.concatenate(cols)
    A = csr_matrix((np.ones(len(rows)), (rows, cols)), shape=(len(M), n))
    r = milp(c=np.ones(n), constraints=LinearConstraint(A, 1, np.inf), integrality=np.ones(n), bounds=Bounds(0, 1),
             options={'time_limit': tl})
    assert r.status == 0, r.message
    return int(round(r.fun))

def tau_bitset(M, n):
    """independent: smallest transversal by enumerating all 2^n sets (n <= 22)."""
    cov = np.zeros(1 << n, np.uint8); cov[np.asarray(M, dtype=np.int64)] = 1
    for i in range(n):
        v = cov.reshape(-1, 2, 1 << i); v[:, 1, :] |= v[:, 0, :]
    # cov[S]=1 iff S contains a member; X is a transversal iff complement of X contains no member
    trans = (cov[::-1] == 0); a = np.flatnonzero(trans)
    return int(pc(a).min())

def count_transversals(M, n, size):
    """number of transversals of exactly `size` points and a few examples (local search cost)."""
    M = np.asarray(M, dtype=np.int64)
    X = np.array([sum(1 << v for v in c) for c in itertools.combinations(range(n), size)], dtype=np.int64)
    bad = np.zeros(len(X), bool)
    for s in range(0, len(X), 4096):
        blk = X[s:s + 4096]
        bad[s:s + 4096] = ((blk[:, None] & M[None, :]) != 0).all(axis=1)
    return int(bad.sum()), X[bad]

def sets_of_size(n, k):
    return np.array([sum(1 << v for v in c) for c in itertools.combinations(range(n), k)], dtype=np.int64)

def save_family(name, M, n, meta):
    np.save(os.path.join(FAM, name + '.npy'), np.asarray(M, dtype=np.int64))
    with open(os.path.join(FAM, name + '.json'), 'w') as f: json.dump(dict(meta, n=n, name=name, members=int(len(M))), f)

def load_family(name):
    M = np.load(os.path.join(FAM, name + '.npy')); meta = json.load(open(os.path.join(FAM, name + '.json'))); return M, meta['n'], meta

# ---------------- distance to the nearest coset family ----------------
def rho_cap(M, n, cap=6):
    """exact min(rho, cap+1) where rho = min wt of a+C(M), C = span of pairwise differences, a in M.  Syndrome method."""
    M = np.asarray(M, dtype=np.int64)
    if len(M) == 1: return min(int(pc(M[0])), cap + 1)
    B = reduced_basis(M ^ M[0], n); H = annihilator(B, n)
    if not H: return 0
    syn = lambda x: sum((bin(h & x).count('1') & 1) << j for j, h in enumerate(H))
    sa = syn(int(M[0])); col = [syn(1 << i) for i in range(n)]
    if sa == 0: return 0
    level = {0: 0}; cur = {0: ()}
    # sums of at most 3 columns, with the smallest number of columns for each value
    for w in range(1, 4):
        nxt = {}
        for s, last in cur.items():
            for i in range(n):
                if last and i <= last[-1]: continue
                t = s ^ col[i]
                if t not in level and t not in nxt: nxt[t] = last + (i,)
        for t in nxt: level[t] = w
        cur = nxt
    best = cap + 1
    for A, wa in level.items():
        wb = level.get(sa ^ A)
        if wb is not None and wa + wb < best: best = wa + wb
    return best

def coset_struct(S, n, dual_enum=22):
    """structure of the coset a + C(S): dim C, codim = n - dim C, rho (capped at 7 = '>=7'), dual distance d^perp = min nonzero
    weight in C^perp (exact when codim <= dual_enum, else None)."""
    S = np.asarray(S, dtype=np.int64)
    if len(S) < 2: return dict(size=int(len(S)), dim=0, codim=n, rho=rho_cap(S, n), dual=None)
    B = reduced_basis(S ^ S[0], n); Hh = annihilator(B, n); c = len(Hh); dual = None
    if 0 < c <= dual_enum:
        A = np.zeros(1, np.int64)
        for h in Hh: A = np.concatenate([A, A ^ h])
        dual = int(pc(A[1:]).min())
    return dict(size=int(len(S)), dim=len(B), codim=c, rho=rho_cap(S, n), dual=dual)

def coset_fractions(M, n, thetas=(1, 2, 3), budget=80, branch=10):
    """For each theta: lower bound on the largest fraction of members in a subfamily H' with rho(H') >= theta
    (best-first search over (functional, side) restrictions; each node's rho is exact).  theta=1 is also solved EXACTLY
    by the Walsh transform: rho(H')>=1 iff H' lies in {x: w.x = 1} for some w != 0.   Returns dict theta -> (frac, exact)."""
    M = np.asarray(M, dtype=np.int64); N = len(M)
    f = np.zeros(1 << n, np.int32); f[M] = 1; hat = fwht(f); n1 = (N - hat) // 2; n1[0] = 0
    ub1 = int(n1.max())
    w1 = int(np.argmax(n1)); S1 = M[(pc(M & w1) & 1) == 1]
    out = {1: (ub1 / N, True, coset_struct(S1, n))}
    del f, hat
    for th in thetas:
        if th == 1: continue
        best = 0; bestS = None; seen = set(); heap = [(-N, 0, M)]; cnt = 0; exp = 0
        while heap and exp < budget:
            negs, _, S = heapq_pop(heap); sz = -negs
            if sz <= best: break
            if len(S) >= 1 and rho_cap(S, n, 6) >= th: best = sz; bestS = S; continue
            exp += 1
            f = np.zeros(1 << n, np.int32); f[S] = 1; hat = fwht(f); m1 = (sz - hat) // 2
            cand = []
            for side in (0, 1):
                cnts = m1 if side else sz - m1
                cnts = cnts.copy(); cnts[0] = 0
                order = np.argpartition(-cnts, min(branch * 3, len(cnts) - 1))[:branch * 3]
                order = order[np.argsort(-cnts[order])]
                for u in order:
                    c = int(cnts[u])
                    if c <= best or c >= sz: continue
                    cand.append((c, int(u), side))
            cand.sort(reverse=True); pushed = 0
            for c, u, side in cand:
                par = pc(S & u) & 1; sub = S[par == side]
                key = hash(sub.tobytes())
                if key in seen: continue
                seen.add(key); cnt += 1; heapq_push(heap, (-len(sub), cnt, sub)); pushed += 1
                if pushed >= branch: break
        out[th] = (best / N, False, coset_struct(bestS, n) if bestS is not None else None)
    return out

import heapq
def heapq_pop(h): return heapq.heappop(h)
def heapq_push(h, x): heapq.heappush(h, x)
