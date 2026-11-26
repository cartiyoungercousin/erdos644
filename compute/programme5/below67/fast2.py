"""Vectorised exact two-block finish (keep all members) and the depth-1 game from a 4-member position.

Two blocks P,Q: WLOG each vertex class gets one label A (in P), B (in Q), AB (both), S (split between P and Q; then
every neighbour is AB), or nothing if it has no neighbour.  (A class using A and AB parts is dominated by relabelling
the AB part A, etc.)  For a labelling with 0/1 vectors cA, cB, cS the least max load is
max(cA.m, cB.m, (cA+cB+cS).m / 2); the finish value is the min over labellings.  Labellings are enumerated once per
graph (backtracking, exact dominance pruning), then evaluated on many mass vectors at once.

Depth-1 game from position (types over 4 members, full mask 15): live types are those with an alive pair
(tau | tau' = 15).  She requests r_tau (total <= t), he answers L with in-mass l_tau <= m_tau - r_tau, total <= 1
(maximal answers dominate).  Final vertices (tau,in), (tau,out); edges for alive (tau1,tau2): in-in, in-out, out-in.
(tau,in) exists iff tau is not fully requested; (tau,out) always (he may leave a point out)."""
import itertools, numpy as np

EPS = 1e-9

def labelings(n, adj, need):
    """adj: list of neighbour sets; need[v]: v has a neighbour.  Labels 0=A 1=B 2=AB 3=S 4=none."""
    out = []
    lab = [None] * n
    order = sorted(range(n), key=lambda v: -len(adj[v]))
    def ok(v, L):
        for w in adj[v]:
            Lw = lab[w]
            if Lw is None: continue
            if (L, Lw) in ((0, 1), (1, 0)): return False
            if L == 3 and Lw != 2: return False
            if Lw == 3 and L != 2: return False
        return True
    def rec(i):
        if i == n:
            out.append(tuple(lab)); return
        v = order[i]
        choices = (0, 1, 2, 3) if need[v] else (4,)
        for L in choices:
            if ok(v, L):
                lab[v] = L; rec(i + 1); lab[v] = None
    rec(0)
    C = np.array([[[1 if L in (0, 2) else 0 for L in l], [1 if L in (1, 2) else 0 for L in l],
                   [1 if L == 3 else 0 for L in l]] for l in out], np.int8)
    # forms: cA, cB, (cA+cB+cS)/2
    F = np.stack([C[:, 0], C[:, 1], (C[:, 0] + C[:, 1] + C[:, 2]) / 2.0], 1)      # (nl, 3, n)
    # dominance pruning (exact): drop l if some l' has all three forms <= (also with A,B swapped)
    key = F.reshape(len(F), -1)
    order = np.argsort(key.sum(1))
    keep = []
    for i in order:
        f = F[i]
        dom = False
        for j in keep[-3000:]:
            g = F[j]
            if np.all(g <= f + EPS) or np.all(g[[1, 0, 2]] <= f + EPS): dom = True; break
        if not dom: keep.append(i)
    return F[keep]

def value(F, M):
    """F: (nl,3,n) forms; M: (N,n) masses -> (N,) least max load"""
    out = np.full(len(M), np.inf)
    for s in range(0, len(M), 4096):
        V = np.einsum('lfn,mn->mlf', F, M[s:s + 4096]).max(axis=2).min(axis=1)
        out[s:s + 4096] = V
    return out

class Pos4:
    """position over 4 members: dict type -> mass (all present)."""
    def __init__(self, types, full=15):
        self.full = full
        self.types = {ty: m for ty, m in types.items()}
        ts = sorted(self.types)
        self.live = [ty for ty in ts if any((ty | u) == full for u in ts if u != ty)]
        self.alive = [(a, b) for i, a in enumerate(self.live) for b in self.live[i + 1:] if (a | b) == full]
        self._cache = {}

    def graph(self, fullset):
        """fullset: frozenset of fully requested live types -> (vertex list, forms)"""
        if fullset in self._cache: return self._cache[fullset]
        verts = []
        for ty in self.live:
            if ty not in fullset: verts.append((ty, 1))
            verts.append((ty, 0))
        vi = {v: i for i, v in enumerate(verts)}
        adj = [set() for _ in verts]
        for (a, b) in self.alive:
            for (sa, sb) in ((1, 1), (1, 0), (0, 1)):
                if (a, sa) in vi and (b, sb) in vi:
                    i, j = vi[(a, sa)], vi[(b, sb)]
                    adj[i].add(j); adj[j].add(i)
        need = [len(a) > 0 for a in adj]
        F = labelings(len(verts), adj, need)
        self._cache[fullset] = (verts, F)
        return verts, F

def grid_vals(m, h):
    if m <= EPS: return [0.0]
    n = int(np.floor(m / h + EPS))
    v = [i * h for i in range(n + 1)]
    if m - v[-1] > EPS: v.append(m)
    return v

def depth1(P, t, h, KK=1.0, want=None, verbose=False):
    """min over requests R (grid h on live types) of max over answers L of the two-block value.
    Returns (value, best R, worst L for it).  want: stop early once a request with value <= want is found."""
    live = P.live; m = np.array([P.types[ty] for ty in live]); n = len(live)
    zero = [i for i in range(n) if m[i] <= EPS]
    pos = [i for i in range(n) if m[i] > EPS]
    best = (np.inf, None, None)
    ranges = [grid_vals(m[i], h) for i in pos]
    for rv in itertools.product(*ranges):
        if sum(rv) > t + EPS: continue
        r = np.zeros(n); r[pos] = rv
        fullset = frozenset([live[i] for i in zero] + [live[i] for i in pos if abs(r[i] - m[i]) <= EPS])
        verts, F = P.graph(fullset)
        avail = m - r
        need = avail.sum() - KK
        # candidate answers (exclusion vectors e on grid, minimal with sum >= need)
        if need <= EPS:
            E = [np.zeros(n)]
        else:
            E = []
            idx = [i for i in range(n) if avail[i] > EPS]
            rg = [grid_vals(avail[i], h) for i in idx]
            for ev in itertools.product(*rg):
                s = sum(ev)
                if s < need - EPS: continue
                if any(ev[j] > EPS and s - min(h, ev[j]) >= need - EPS for j in range(len(ev))): continue
                e = np.zeros(n); e[idx] = ev; E.append(e)
        E = np.array(E)
        Lin = avail[None, :] - E                       # in-mass
        M = np.zeros((len(E), len(verts)))
        for k, (ty, s) in enumerate(verts):
            i = live.index(ty)
            M[:, k] = Lin[:, i] if s == 1 else (m[i] - Lin[:, i])
        val = value(F, M)
        j = int(np.argmax(val)); v = val[j]
        if v < best[0]:
            best = (v, r.copy(), Lin[j].copy())
            if verbose: print('  R=%s -> %.5f' % (np.round(r, 4), v), flush=True)
            if want is not None and v <= want + EPS: break
    return best

from scipy.optimize import milp, LinearConstraint, Bounds

def adv_best(F, verts, live, m, r, KK=1.0):
    """exact adversary best answer to request r (continuous L): max over exclusions e of min over labellings of max
    over the three forms.  Returns (value, in-mass vector)."""
    n = len(live)
    avail = m - r
    need = avail.sum() - KK
    li = {ty: i for i, ty in enumerate(live)}
    # M = M0 + D e   (e over all n live types; e_i <= avail_i)
    nv = len(verts)
    M0 = np.zeros(nv); D = np.zeros((nv, n))
    for k, (ty, s) in enumerate(verts):
        i = li[ty]
        if s == 1: M0[k] = avail[i]; D[k, i] = -1
        else: M0[k] = r[i]; D[k, i] = 1
    if need <= EPS:
        v = value(F, M0[None, :])[0]
        return v, avail.copy()
    nl = len(F)
    C = F @ M0            # (nl,3)
    Dd = np.einsum('lfk,ki->lfi', F, D)   # (nl,3,n)
    # vars: e (n), s (1), z (nl*3)
    nz = nl * 3; NV = n + 1 + nz
    BIG = 4.0
    rows = []; lo = []; hi = []
    from scipy.sparse import lil_matrix
    A = lil_matrix((nz + nl + 1, NV))
    row = 0
    for l in range(nl):
        for f in range(3):
            # s - Dd e + BIG z <= C + BIG
            A[row, n] = 1
            for i in range(n):
                if Dd[l, f, i] != 0: A[row, i] = -Dd[l, f, i]
            A[row, n + 1 + 3 * l + f] = BIG
            lo.append(-np.inf); hi.append(C[l, f] + BIG); row += 1
        for f in range(3): A[row, n + 1 + 3 * l + f] = 1
        lo.append(1); hi.append(np.inf); row += 1
    for i in range(n): A[row, i] = 1
    lo.append(need); hi.append(need); row += 1
    c = np.zeros(NV); c[n] = -1
    integ = np.zeros(NV); integ[n + 1:] = 1
    lb = np.zeros(NV); ub = np.concatenate([np.maximum(avail, 0), [BIG], np.ones(nz)])
    res = milp(c, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=integ, bounds=Bounds(lb, ub),
               options={'disp': False, 'mip_rel_gap': 1e-9})
    e = res.x[:n]
    Lin = avail - e
    M = M0 + D @ e
    return value(F, M[None, :])[0], Lin

def depth1x(P, t, h, KK=1.0, want=None, verbose=False, maximal=True):
    """as depth1, but the adversary's answer is exact (MILP over continuous L); her requests on the grid h,
    maximal requests only (total = t, or everything live requested)."""
    live = P.live; m = np.array([P.types[ty] for ty in live]); n = len(live)
    zero = [i for i in range(n) if m[i] <= EPS]
    pos = [i for i in range(n) if m[i] > EPS]
    best = (np.inf, None, None)
    ranges = [grid_vals(m[i], h) for i in pos]
    tot = m.sum()
    for rv in itertools.product(*ranges):
        s = sum(rv)
        if s > t + EPS: continue
        if maximal and s + h <= t + EPS and s < tot - EPS:
            continue
        r = np.zeros(n); r[pos] = rv
        fullset = frozenset([live[i] for i in zero] + [live[i] for i in pos if abs(r[i] - m[i]) <= EPS])
        verts, F = P.graph(fullset)
        v, Lin = adv_best(F, verts, live, m, r, KK)
        if v < best[0]:
            best = (v, r.copy(), Lin.copy())
            if verbose: print('  R=%s -> %.5f' % (np.round(r, 4), v), flush=True)
            if want is not None and v <= want + EPS: break
    return best

def _excl_cands(avail, need, rng, nrand=40):
    n = len(avail); idx = [i for i in range(n) if avail[i] > EPS]
    C = []
    def spill(e):
        rem = need - e.sum()
        for i in idx:
            if rem <= EPS: break
            add = min(avail[i] - e[i], rem); e[i] += add; rem -= add
        return e if rem <= EPS else None
    for i in idx:
        for j in idx:
            for lam in (0.0, 0.25, 0.5, 0.75, 1.0):
                e = np.zeros(n); e[i] = min(avail[i], lam * need)
                e[j] += min(avail[j] - e[j], need - e[i])
                e = spill(e)
                if e is not None: C.append(e)
    for _ in range(nrand):
        w = rng.dirichlet(np.ones(len(idx)) * 0.5)
        e = np.zeros(n); e[idx] = np.minimum(avail[idx], w * need)
        e = spill(e)
        if e is not None: C.append(e)
    return np.array(C)

def depth1f(P, t, h, KK=1.0, want=None, seed=0):
    """fast depth-1: her maximal grid requests; his answer: heuristic candidates first (a found value > t is a
    genuine spoiler), exact MILP only when the candidates do not spoil.  Returns (v, R, L, exact_flag):
    v > t  => every grid request is spoiled (sound); v <= t => R closes (exact MILP check)."""
    rng = np.random.default_rng(seed)
    live = P.live; m = np.array([P.types[ty] for ty in live]); n = len(live)
    zero = [i for i in range(n) if m[i] <= EPS]
    pos = [i for i in range(n) if m[i] > EPS]
    tot = m.sum()
    li = {ty: i for i, ty in enumerate(live)}
    best = (np.inf, None, None, False)
    for rv in itertools.product(*[grid_vals(m[i], h) for i in pos]):
        s = sum(rv)
        if s > t + EPS or (s + h <= t + EPS and s < tot - EPS): continue
        r = np.zeros(n); r[pos] = rv
        fullset = frozenset([live[i] for i in zero] + [live[i] for i in pos if abs(r[i] - m[i]) <= EPS])
        verts, F = P.graph(fullset)
        avail = m - r; need = avail.sum() - KK
        E = np.zeros((1, n)) if need <= EPS else _excl_cands(avail, need, rng)
        Lin = avail[None, :] - E
        M = np.zeros((len(E), len(verts)))
        for k, (ty, sgn) in enumerate(verts):
            i = li[ty]; M[:, k] = Lin[:, i] if sgn == 1 else (m[i] - Lin[:, i])
        val = value(F, M); j = int(np.argmax(val)); v = val[j]; Lw = Lin[j]; ex = need <= EPS
        if v <= t + EPS and not ex:
            v, Lw = adv_best(F, verts, live, m, r, KK); ex = True
        if v < best[0]:
            best = (v, r.copy(), Lw.copy(), ex)
            if want is not None and v <= want + EPS: break
    return best

def adv_best_S(F, verts, P, m, r, Sint, KK=1.0, nmem=4):
    """as adv_best, but his answer L must have every trace (on members bit 0..nmem-1) in the spectrum
    Sint = list of closed intervals; he may also put L-points on dead types (no pairs) and outside V."""
    live = P.live; n = len(live)
    dead = [ty for ty in sorted(P.types) if ty not in live]
    nd = len(dead)
    avail = m - r
    li = {ty: i for i, ty in enumerate(live)}
    nv = len(verts)
    M0 = np.zeros(nv); D = np.zeros((nv, n))
    for k, (ty, s) in enumerate(verts):
        i = li[ty]
        if s == 1: M0[k] = avail[i]; D[k, i] = -1
        else: M0[k] = r[i]; D[k, i] = 1
    nl = len(F)
    C = F @ M0; Dd = np.einsum('lfk,ki->lfi', F, D)
    nz = nl * 3; ni = len(Sint)
    # vars: e(n) d(nd) s z(nz) w(nmem*ni)
    oE, oD, oS, oZ, oW = 0, n, n + nd, n + nd + 1, n + nd + 1 + nz
    NV = oW + nmem * ni
    BIG = 4.0
    from scipy.sparse import lil_matrix
    A = lil_matrix((nz + nl + 1 + nmem * (2 * ni + 1) + 2, NV)); lo = []; hi = []; row = 0
    for l in range(nl):
        for f in range(3):
            A[row, oS] = 1
            for i in range(n):
                if Dd[l, f, i] != 0: A[row, oE + i] = -Dd[l, f, i]
            A[row, oZ + 3 * l + f] = BIG; lo.append(-np.inf); hi.append(C[l, f] + BIG); row += 1
        for f in range(3): A[row, oZ + 3 * l + f] = 1
        lo.append(1); hi.append(np.inf); row += 1
    # total in V <= KK:  sum(avail - e) + sum d <= KK
    for i in range(n): A[row, oE + i] = -1
    for j in range(nd): A[row, oD + j] = 1
    lo.append(-np.inf); hi.append(KK - avail.sum()); row += 1
    for b in range(nmem):
        # trace = sum_{live ty with bit b} (avail - e) + sum_{dead ty with bit b} d
        c0 = sum(avail[i] for i, ty in enumerate(live) if ty >> b & 1)
        for k, (lo_, hi_) in enumerate(Sint):
            # w=1 => trace >= lo_:   sum e - sum d + BIG w <= c0 - lo_ + BIG
            for i, ty in enumerate(live):
                if ty >> b & 1: A[row, oE + i] = 1
            for j, ty in enumerate(dead):
                if ty >> b & 1: A[row, oD + j] = -1
            A[row, oW + b * ni + k] = BIG; lo.append(-np.inf); hi.append(c0 - lo_ + BIG); row += 1
            # w=1 => trace <= hi_:  -sum e + sum d + BIG w <= hi_ + BIG - c0
            for i, ty in enumerate(live):
                if ty >> b & 1: A[row, oE + i] = -1
            for j, ty in enumerate(dead):
                if ty >> b & 1: A[row, oD + j] = 1
            A[row, oW + b * ni + k] = BIG; lo.append(-np.inf); hi.append(hi_ + BIG - c0); row += 1
        for k in range(ni): A[row, oW + b * ni + k] = 1
        lo.append(1); hi.append(np.inf); row += 1
    A = A[:row]
    c = np.zeros(NV); c[oS] = -1
    integ = np.zeros(NV); integ[oZ:] = 1
    lb = np.zeros(NV)
    deadm = np.array([P.types[ty] for ty in dead]) if nd else np.zeros(0)
    ub = np.concatenate([np.maximum(avail, 0), deadm, [BIG], np.ones(nz + nmem * ni)])
    res = milp(c, constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=integ, bounds=Bounds(lb, ub),
               options={'disp': False, 'mip_rel_gap': 1e-9})
    if res.status != 0: return -np.inf, None
    e = res.x[:n]; M = M0 + D @ e
    return value(F, M[None, :])[0], avail - e

def depth1xS(P, t, h, Sint, KK=1.0, want=None):
    live = P.live; m = np.array([P.types[ty] for ty in live]); n = len(live)
    zero = [i for i in range(n) if m[i] <= EPS]; pos = [i for i in range(n) if m[i] > EPS]
    best = (np.inf, None, None); tot = m.sum()
    for rv in itertools.product(*[grid_vals(m[i], h) for i in pos]):
        s = sum(rv)
        if s > t + EPS or (s + h <= t + EPS and s < tot - EPS): continue
        r = np.zeros(n); r[pos] = rv
        fs = frozenset([live[i] for i in zero] + [live[i] for i in pos if abs(r[i] - m[i]) <= EPS])
        verts, F = P.graph(fs)
        v, Lin = adv_best_S(F, verts, P, m, r, Sint, KK)
        if v < best[0]:
            best = (v, r.copy(), Lin)
            if want is not None and v <= want + EPS: break
    return best
