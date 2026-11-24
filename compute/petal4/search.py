"""PETAL 24/25 small-ground-set search (blow-up families, two classes).
Exhaustive over atom-size multisets (sorted, nonincreasing = symmetry breaking), exact SAT (CaDiCaL) per size vector
over ALL type subsets (no cap on #types per class), with CEGAR on AP(H) >= T+2.
usage: py search.py k m_max n_lo n_hi [start_idx] [time_limit_s]"""
import sys, time, itertools
import numpy as np
from pysat.solvers import Glucose4


def comps(total, bounds):
    """all vectors e, 0<=e_i<=bounds_i, sum=total"""
    m = len(bounds); out = []

    def rec(i, rem, cur):
        if i == m - 1:
            if rem <= bounds[i]: out.append(cur + [rem])
            return
        rest = sum(bounds[i + 1:])
        for v in range(max(0, rem - rest), min(bounds[i], rem) + 1):
            rec(i + 1, rem - v, cur + [v])
    rec(0, total, []); return out


def partitions(n, maxparts, maxpart):
    def rec(rem, parts_left, mx):
        if rem == 0: yield []; return
        if parts_left == 0: return
        for v in range(min(rem, mx), 0, -1):
            if v * parts_left < rem: break
            for r in rec(rem - v, parts_left - 1, v): yield [v] + r
    yield from rec(n, maxparts, maxpart)


def killset(s, e, x):  # does request x meet every edge of type e
    return any(ei > si - xi for si, ei, xi in zip(s, e, x))


def h_inside(s, types, R):
    """least sum x, x_i=0 outside R, killing all types; huge if impossible. DP over atoms with bitmasks."""
    INF = 10**9
    if not types: return 0
    full = (1 << len(types)) - 1
    dp = {0: 0}
    for i in R:
        opts = {0: 0}
        for lvl in range(1, s[i] + 1):
            mk = 0
            for j, e in enumerate(types):
                if e[i] > s[i] - lvl: mk |= 1 << j
            if mk not in opts or opts[mk] > lvl: opts[mk] = lvl
        nd = dict(dp)
        for m0, c0 in dp.items():
            for mk, lv in opts.items():
                m1 = m0 | mk; c1 = c0 + lv
                if m1 not in nd or nd[m1] > c1: nd[m1] = c1
        dp = nd
    return dp.get(full, INF)


def ap_union(s, X, Y, T):
    """AP over atom-union disjoint region pairs (R_X,R_Y) and both roles. returns (min cost, witness)"""
    m = len(s); best = (10**9, None)
    for assign in itertools.product((0, 1, 2), repeat=m):  # 0 none,1 R_X,2 R_Y
        RX = [i for i in range(m) if assign[i] == 1]; RY = [i for i in range(m) if assign[i] == 2]
        bX = max(sum(e[i] for i in range(m) if assign[i] != 1) for e in X)
        bY = max(sum(e[i] for i in range(m) if assign[i] != 2) for e in Y)
        hX = h_inside(s, X, RX); hY = h_inside(s, Y, RY)
        c1 = max(hX, 2 * bY) + -(-8 * bX // 3) + 2   # X petal
        c2 = max(hY, 2 * bX) + -(-8 * bY // 3) + 2   # Y petal
        for c, role in ((c1, 'X'), (c2, 'Y')):
            if c < best[0]: best = (c, (assign, role, bX, bY, hX, hY))
    return best


def out_mass(e, s, r):
    return sum(min(e[i], s[i] - r[i]) for i in range(len(s)))


def h_counts(s, types, r):
    """least request x with x_i <= r_i (point region with r_i points in atom i) killing all types; 10**9 if none"""
    INF = 10**9
    if not types: return 0
    full = (1 << len(types)) - 1; dp = {0: 0}
    for i in range(len(s)):
        if r[i] == 0: continue
        opts = {0: 0}
        for lvl in range(1, r[i] + 1):
            mk = 0
            for j, e in enumerate(types):
                if e[i] > s[i] - lvl: mk |= 1 << j
            if mk not in opts or opts[mk] > lvl: opts[mk] = lvl
        nd = dict(dp)
        for m0, c0 in dp.items():
            for mk, lv in opts.items():
                m1 = m0 | mk; c1 = c0 + lv
                if m1 not in nd or nd[m1] > c1: nd[m1] = c1
        dp = nd
    return dp.get(full, INF)


def ap_value(s, X, Y, T):
    """TRUE AP over point-set region pairs. By symmetry only counts matter; cost is monotone (bigger regions are better
    for the petal class: beta and h both shrink), so only partitions r^X + r^Y = s are needed.
    returns (min cost, witness=(role, rP, rQ, bP, bQ, hP, Pclass))"""
    m = len(s); best = (10**9, None)
    for rX in itertools.product(*[range(v + 1) for v in s]):
        rY = tuple(s[i] - rX[i] for i in range(m))
        bX = max(out_mass(e, s, rX) for e in X); bY = max(out_mass(e, s, rY) for e in Y)
        hX = h_counts(s, X, rX); hY = h_counts(s, Y, rY)
        c1 = max(hX, 2 * bY) + -(-8 * bX // 3) + 2
        c2 = max(hY, 2 * bX) + -(-8 * bY // 3) + 2
        if c1 < best[0]: best = (c1, ('X', rX, rY, bX, bY, hX))
        if c2 < best[0]: best = (c2, ('Y', rY, rX, bY, bX, hY))
    return best


def tau_blowup(s, types):
    """tau by request enumeration"""
    for t in range(0, sum(s) + 1):
        for x in comps(t, s):
            if all(killset(s, e, x) for e in types): return t
    return sum(s)


def ap_value_split(s, X, Y, T):
    """AP over region pairs that may split atoms (counts r^X_i + r^Y_i <= s_i); exact by symmetry."""
    m = len(s)
    best = 10**9

    def beta(types, r):
        return max(sum(min(e[i], s[i] - r[i]) for i in range(m)) for e in types)

    def hh(types, r):
        INF = 10**9
        full = (1 << len(types)) - 1; dp = {0: 0}
        for i in range(m):
            if r[i] == 0: continue
            opts = {0: 0}
            for lvl in range(1, r[i] + 1):
                mk = 0
                for j, e in enumerate(types):
                    if e[i] > s[i] - lvl: mk |= 1 << j
                if mk not in opts or opts[mk] > lvl: opts[mk] = lvl
            nd = dict(dp)
            for m0, c0 in dp.items():
                for mk, lv in opts.items():
                    m1 = m0 | mk; c1 = c0 + lv
                    if m1 not in nd or nd[m1] > c1: nd[m1] = c1
            dp = nd
        return dp.get(full, INF)
    ranges = [[(a, b) for a in range(s[i] + 1) for b in range(s[i] + 1 - a)] for i in range(m)]
    for rr in itertools.product(*ranges):
        rX = [p[0] for p in rr]; rY = [p[1] for p in rr]
        bX = beta(X, rX); bY = beta(Y, rY)
        hX = hh(X, rX); hY = hh(Y, rY)
        c1 = max(hX, 2 * bY) + -(-8 * bX // 3) + 2
        c2 = max(hY, 2 * bX) + -(-8 * bY // 3) + 2
        best = min(best, c1, c2)
    return best


def comps_sub(s, R, total):
    """requests with support in atoms R, sum = total (<= s_i)"""
    if total == 0: yield [0] * len(s); return
    b = [s[i] if i in R else 0 for i in range(len(s))]
    if sum(b) < total: return
    yield from comps(total, b)


def solve_size(s, k, c, mu, T, deadline=None, ap_cegar=True):
    m = len(s)
    types = comps(k, s)
    E = np.array(types, dtype=np.int32) if types else np.zeros((0, m), dtype=np.int32)
    S = np.array(s, dtype=np.int32)
    selfov = np.maximum(0, 2 * E - S).sum(1) if len(E) else np.zeros(0)
    E = E[selfov >= c]; N = len(E)
    if N == 0: return dict(status='INFEAS', reason='no self-overlapping type', N=0)
    types = [tuple(int(v) for v in r) for r in E]
    reqs = comps(T, s)
    R = np.array(reqs, dtype=np.int32)
    comp = S[None, :] - R
    solver = Glucose4()
    xv = lambda i: i + 1
    yv = lambda i: N + i + 1
    for r in range(len(reqs)):
        surv = np.nonzero((E <= comp[r][None, :]).all(1))[0]
        if len(surv) == 0:
            solver.delete(); return dict(status='INFEAS', reason='request kills every self-overlapping type', N=N)
        solver.add_clause([xv(int(i)) for i in surv] + [yv(int(i)) for i in surv])
    for a0 in range(0, N, 128):
        A = E[a0:a0 + 128]
        mn = np.maximum(0, A[:, None, :] + E[None, :, :] - S[None, None, :]).sum(2)
        mx = np.minimum(A[:, None, :], E[None, :, :]).sum(2)
        ii, jj = np.nonzero(mn < c)
        for a, b in zip(ii, jj):
            a = int(a) + a0; b = int(b)
            if a < b:
                solver.add_clause([-xv(a), -xv(b)]); solver.add_clause([-yv(a), -yv(b)])
        ii, jj = np.nonzero(mx > mu)
        for a, b in zip(ii, jj):
            a = int(a) + a0; b = int(b)
            solver.add_clause([-xv(a), -yv(b)])
    solver.add_clause([xv(i) for i in range(N)]); solver.add_clause([yv(i) for i in range(N)])
    for t in range(N):  # X/Y symmetry: smallest-index chosen type lies in X
        solver.add_clause([-yv(t)] + [xv(u) for u in range(t)])
    nrange = 0; info = dict(N=N, nreq=len(reqs), cegar=0)
    while True:
        if deadline and time.time() > deadline:
            solver.delete(); info['status'] = 'TIMEOUT'; return info
        if not solver.solve():
            solver.delete()
            info['status'] = 'INFEAS' if nrange == 0 else 'NO_HIT_RANGE_FEASIBLE'
            info['range_models'] = nrange; return info
        model = set(l for l in solver.get_model() if l > 0)
        X = [types[i] for i in range(N) if xv(i) in model]; Y = [types[i] for i in range(N) if yv(i) in model]
        nrange += 1
        if not ap_cegar:
            solver.delete(); info.update(status='RANGE_FEASIBLE', X=X, Y=Y); return info
        ap, wit = ap_value(s, X, Y, T)
        if ap >= T + 2:
            solver.delete(); info.update(status='HIT', X=X, Y=Y, AP=ap); return info
        info['cegar'] += 1
        Pc, rP, rQ, bP, bQ, hP = wit
        Qc = 'Y' if Pc == 'X' else 'X'
        Ptypes = X if Pc == 'X' else Y
        xs = None
        for xx in comps(hP, list(rP)) if hP > 0 else [[0] * m]:
            if all(killset(s, e, xx) for e in Ptypes): xs = xx; break
        variants = set()
        for bp in range(bP, k + 1):
            for bq in range(bQ, k + 1):
                if max(hP, 2 * bq) + -(-8 * bp // 3) + 2 <= T + 1: variants.add((bp, bq))
        var = [v for v in variants if not any(w != v and w[0] >= v[0] and w[1] >= v[1] for w in variants)]
        vP = xv if Pc == 'X' else yv; vQ = xv if Qc == 'X' else yv
        for bp, bq in var:
            aP = set(i for i in range(N) if out_mass(types[i], s, rP) <= bp and killset(s, types[i], xs))
            aQ = set(i for i in range(N) if out_mass(types[i], s, rQ) <= bq)
            solver.add_clause([vP(i) for i in range(N) if i not in aP] + [vQ(i) for i in range(N) if i not in aQ])


if __name__ == '__main__':
    k = int(sys.argv[1]); m_max = int(sys.argv[2]); n_lo = int(sys.argv[3]); n_hi = int(sys.argv[4])
    start = int(sys.argv[5]) if len(sys.argv) > 5 else 0
    tl = float(sys.argv[6]) if len(sys.argv) > 6 else 1500
    min_m = int(sys.argv[7]) if len(sys.argv) > 7 else 1
    c = {12: 7, 16: 9}[k]; T = 3 * k // 4; mu = c - 1
    sizes = []
    for n in range(n_lo, n_hi + 1):
        for p in partitions(n, m_max, 2 * k):
            if len(p) >= min_m: sizes.append(tuple(p))
    print('k', k, 'c', c, 'mu', mu, 'T', T, 'size vectors', len(sizes), flush=True)
    t0 = time.time(); deadline = t0 + tl
    stats = {}
    for idx in range(start, len(sizes)):
        s = sizes[idx]
        if time.time() > deadline: print('STOPPED_TIME at idx', idx, flush=True); break
        t1 = time.time()
        r = solve_size(list(s), k, c, mu, T, deadline=deadline)
        st = r['status']; stats[st] = stats.get(st, 0) + 1
        if st in ('HIT','TIMEOUT') or idx % 500 == 0:
            print(idx, s, st, {a: b for a, b in r.items() if a not in ('X', 'Y')}, 'X', r.get('X'), 'Y', r.get('Y'), '%.1fs' % (time.time() - t1), flush=True)
        if st == 'TIMEOUT': print('STOPPED_TIME at idx', idx, flush=True); break
    else:
        print('DONE all size vectors', flush=True)
    print('STATS', stats, 'elapsed %.0fs' % (time.time() - t0), flush=True)
