r"""Programme 4 / cells: exact search over PROFILE families (independent re-implementation).

Profile family: V = X_1 u ... u X_q, |X_i| = a_i, H_J = {B in C(V,k) : (|B n X_i|)_i in J}.

Criteria used (derived in notes/PROGRAMME4_CELLS.md, tested against explicit enumeration in brute.py):
 (tau)   tau(H_J) > T  iff  for every u with sum u = T, 0 <= u <= a, some j in J has j <= a - u.
 (seven) H_J has a good seven iff there are integers x[i][S] >= 0 (i a cell, S a nonempty subset of [7], the
         co-type: the members of the seven that MISS the point) with sum_S x[i][S] = a_i, the support
         {S : some x[i][S] > 0} pairwise intersecting, and for every m in [7] the profile
         p_m = (sum_{S not containing m} x[i][S])_i  lies in J.        (all 127 co-types; no Fano restriction)
Monotone form used for cuts: if the support is pairwise intersecting and A_m = (sum_{S not containing m} x[i][S])_i,
then J containing some j_m <= A_m for every m already gives a good seven (take B_m inside the available points).

CEGAR: a SAT solver (CaDiCaL) proposes J satisfying all (tau) clauses and all cuts; CP-SAT looks for a good seven
in H_J; if one exists, its types are shrunk greedily (keeping the support intersecting) and the cut
"J misses one of the seven boxes {j : j <= A_m}" is added.  Terminates with UNSAT (certificate = list of cuts,
each with its witnessing x) or with a seven-free covering J.
"""
import itertools, json, os, sys, time
from functools import lru_cache
from ortools.sat.python import cp_model
from pysat.solvers import Cadical153

TYPES = list(range(1, 128))                      # nonempty subsets of [7] as bitmasks
DISJ = [(S, T) for S in TYPES for T in TYPES if S < T and S & T == 0]


def compositions(total, caps):
    """all tuples u with sum u = total, 0 <= u_i <= caps_i"""
    q = len(caps)
    if q == 1:
        if 0 <= total <= caps[0]:
            yield (total,)
        return
    rest = sum(caps[1:])
    for v in range(max(0, total - rest), min(caps[0], total) + 1):
        for t in compositions(total - v, caps[1:]):
            yield (v,) + t


def universe(a, k):
    return list(compositions(k, [min(ai, k) for ai in a]))


def leq(j, b):
    return all(x <= y for x, y in zip(j, b))


def cover_sets(a, k, T, U):
    """for each u (sum T) the set of profile indices j <= a - u; None if some set is empty (tau <= T for all J)"""
    out = set()
    for u in compositions(T, list(a)):
        b = tuple(ai - ui for ai, ui in zip(a, u))
        c = frozenset(t for t, j in enumerate(U) if leq(j, b))
        if not c:
            return None
        out.add(c)
    # drop supersets (subsumed clauses)
    out = sorted(out, key=len)
    kept = []
    for c in out:
        if not any(d <= c for d in kept):
            kept.append(c)
    return kept


def tau_of(a, k, Jset):
    """exact tau of H_J via criterion (tau): smallest T such that some u (sum T) has no j <= a - u"""
    n = sum(a)
    for T in range(0, n + 1):
        for u in compositions(T, list(a)):
            b = tuple(ai - ui for ai, ui in zip(a, u))
            if not any(leq(j, b) for j in Jset):
                return T
    return n + 1


def find_seven(a, k, Jlist, time_limit=600.0, workers=1, types=None):
    """CP-SAT search for a good seven in H_J. Returns (status, x) with x = {cell: {S: count}} or None.
    status in 'FOUND', 'NONE' (proved infeasible), 'UNKNOWN'."""
    q = len(a)
    types = TYPES if types is None else types
    md = cp_model.CpModel()
    y = {S: md.NewBoolVar(f"y{S}") for S in types}
    tset = set(types)
    for S, T in DISJ:
        if S in tset and T in tset:
            md.AddBoolOr([y[S].Not(), y[T].Not()])
    x = {}
    for i in range(q):
        for S in types:
            x[i, S] = md.NewIntVar(0, a[i], f"x{i}_{S}")
            md.Add(x[i, S] == 0).OnlyEnforceIf(y[S].Not())
        md.Add(sum(x[i, S] for S in types) == a[i])
    tuples = [(t,) + tuple(j) for t, j in enumerate(Jlist)]
    idx = []
    for m in range(7):
        p = []
        for i in range(q):
            v = md.NewIntVar(0, a[i], f"p{m}_{i}")
            md.Add(v == sum(x[i, S] for S in types if not (S >> m) & 1))
            p.append(v)
        it = md.NewIntVar(0, len(Jlist) - 1, f"idx{m}")
        md.AddAllowedAssignments([it] + p, tuples)
        idx.append(it)
    for m in range(6):                                   # members unordered: sort them (relabelling [7])
        md.Add(idx[m] <= idx[m + 1])
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = time_limit
    s.parameters.num_workers = workers
    st = s.Solve(md)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        xs = {i: {S: s.Value(x[i, S]) for S in types if s.Value(x[i, S]) > 0} for i in range(q)}
        return 'FOUND', xs
    if st == cp_model.INFEASIBLE:
        return 'NONE', None
    return 'UNKNOWN', None


def avail(a, xs):
    q = len(a)
    return [tuple(sum(c for S, c in xs[i].items() if not (S >> m) & 1) for i in range(q)) for m in range(7)]


def shrink(xs):
    """greedily shrink co-types (all points of a type together) keeping the support pairwise intersecting"""
    q = len(xs)
    sup = sorted(set(S for i in xs for S in xs[i]), key=lambda S: -bin(S).count('1'))
    cur = list(sup)
    changed = True
    while changed:
        changed = False
        for t in range(len(cur)):
            S = cur[t]
            for e in range(7):
                if not (S >> e) & 1:
                    continue
                S2 = S & ~(1 << e)
                if S2 == 0:
                    continue
                if all(S2 & cur[u] for u in range(len(cur)) if u != t):
                    cur[t] = S2; S = S2; changed = True
    mp = dict(zip(sup, cur))
    out = {i: {} for i in xs}
    for i in xs:
        for S, c in xs[i].items():
            out[i][mp[S]] = out[i].get(mp[S], 0) + c
    return out


def check_seven_config(a, k, xs):
    """independent sanity check of a stored seven configuration (used also by checker)"""
    sup = set(S for i in xs for S in xs[i] if xs[i][S] > 0)
    assert all(1 <= S < 128 for S in sup)
    assert all(S & T for S in sup for T in sup), "support not intersecting"
    for i in range(len(a)):
        assert sum(xs[i].values()) == a[i]
    A = avail(a, xs)
    assert all(sum(Am) >= k for Am in A)
    return A


def minimize_J(J, covers):
    """drop profiles while every cover set is still hit (J as set of indices)"""
    J = set(J)
    for t in sorted(J):
        J.discard(t)
        if not all(c & J for c in covers):
            J.add(t)
    return J


def solve_instance(a, k, T, time_limit=600.0, workers=1, log=None, max_iter=10 ** 6):
    a = tuple(a)
    U = universe(a, k)
    covers = cover_sets(a, k, T, U)
    res = dict(a=list(a), k=k, T=T, n=sum(a), nU=len(U))
    if covers is None:
        res.update(status='TRIVIAL', cuts=[])
        return res
    sat = Cadical153()
    for c in covers:
        sat.add_clause([t + 1 for t in sorted(c)])
    nv = len(U)
    boxvar = {}
    cuts = []
    t0 = time.time()
    while True:
        if len(cuts) >= max_iter:
            res.update(status='ITER_LIMIT'); break
        if not sat.solve():
            res.update(status='UNSAT'); break
        model = sat.get_model()
        pos = set(l for l in model if l > 0)
        J = {t for t in range(len(U)) if t + 1 in pos}
        J = minimize_J(J, covers)
        Jl = [U[t] for t in sorted(J)]
        st, xs = find_seven(a, k, Jl, time_limit, workers)
        if st == 'FOUND':
            xs = shrink(xs)
            A = check_seven_config(a, k, xs)
            lits = []
            for Am in A:
                box = frozenset(t for t, j in enumerate(U) if leq(j, Am))
                if box not in boxvar:
                    nv += 1; boxvar[box] = nv
                    for t in box:
                        sat.add_clause([-nv, -(t + 1)])
                lits.append(boxvar[box])
            sat.add_clause(sorted(set(lits)))
            cuts.append({str(i): {str(S): c for S, c in xs[i].items()} for i in xs})
        elif st == 'NONE':
            res.update(status='SEVEN_FREE', J=[list(j) for j in Jl], tau=tau_of(a, k, Jl)); break
        else:
            res.update(status='UNKNOWN', J=[list(j) for j in Jl]); break
    res['cuts'] = cuts
    res['ncuts'] = len(cuts)
    res['secs'] = round(time.time() - t0, 2)
    sat.delete()
    return res


def splits(n, q, amin=1):
    """nondecreasing a_1 <= ... <= a_q, a_i >= amin, sum n"""
    def rec(rem, parts, lo):
        if parts == 1:
            if rem >= lo:
                yield (rem,)
            return
        for v in range(lo, rem // parts + 1):
            for t in rec(rem - v, parts - 1, v):
                yield (v,) + t
    return list(rec(n, q, amin))


if __name__ == '__main__':
    # usage: cells.py k T a1 a2 ... (single instance)
    k, T = int(sys.argv[1]), int(sys.argv[2]); a = tuple(int(v) for v in sys.argv[3:])
    r = solve_instance(a, k, T)
    print(json.dumps({kk: v for kk, v in r.items() if kk != 'cuts'}))
