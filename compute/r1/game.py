"""R1: looseness-constrained request game, one adaptive round (normalized k = 1).

Objects
-------
Good triple E,F,G with pair cells X=E&F, Y=E&G, Z=F&G (sizes x,y,z) and private parts PE,PF,PG.
First request D: d_c points of each of the six cells, sum = t.
Response K: k_c <= mass_c - d_c points of each cell, k_N new points, total 1.
The four edges E,F,G,K cut the known points into 13 regions: (c, in K) = "c+", (c, not in K) =
"c-", and N (new points of K).

Closures available to the requester after K (all STATIC, requests inside the known points)
  Q : keep E,F,G,K, 3 requests;
  T_c (c in X,Y,Z, only if cell c is sealed, see below): drop the edge opposite to c, i.e. keep
      the good triple formed by K and the two edges through c, 4 requests ("re-anchoring").
A closure wins if all request loads are <= t.  Values are computed from the exact pattern tables
of tables.py:  value = min_pattern max_lambda  W[pattern, lambda] . (class masses).

Honest treatment of emptiness.  A region is *structurally empty* if its cell has mass 0, or if
it is c+ and c is entirely inside D ("sealed").  Every other region is treated as PRESENT even
when the adversary gives it mass 0, because the adversary can put O(1) points there for free.
In particular (E,F,K) is a good triple -- so that the looseness inequality applies to it and it
can be used as a new anchor -- only when X is sealed; similarly Y for (E,G,K), Z for (F,G,K).

Adversary.  K ranges over
   0 <= k_c <= mass_c - d_c,  k_N >= 0,  sum = 1,
   plus the rules of class Rules / make_rules (all of them concern only good triples created by
   the response, i.e. sealed cells): looseness S' <= 3 - 2t, and optionally an extremal-anchor
   rule (maxS, minS, pot:a,b,c, poth:a,b,c) or the pair rule (M, MS).
For a finite pool of patterns the question "is there an admissible K that defeats every pattern
of the pool by margin mu" is a MILP (one binary per pattern and lambda).  Constraint generation:
solve it; evaluate the exact closure value at the K found (all patterns); if it is > t the
adversary wins this D; otherwise add the best patterns to the pool and repeat.  If the MILP
optimum is mu <= tol the requester wins this D, and the pool is a finite certificate.

Speed: closures are evaluated on sampled sub-tables (tables.fast_index); a claimed adversary win
is always confirmed on the complete tables (set R1_FULL_TABLES=1 to use only complete tables).
"""
from __future__ import annotations
import itertools, os
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
import numpy as np
import pulp
import tables

E_, F_, G_, K_ = 1, 2, 4, 8
CELL_NAMES = ["X", "Y", "Z", "PE", "PF", "PG"]
CELL_MEM = [E_ | F_, E_ | G_, F_ | G_, E_, F_, G_]
NREG = 13
REG_NAME = [f"{c}{'+' if b else '-'}" for c in CELL_NAMES for b in (1, 0)] + ["N"]
REG_MEM = [m | (K_ if b else 0) for m in CELL_MEM for b in (1, 0)] + [K_]
REG_CELL = [i for i in range(6) for b in (1, 0)] + [None]
REG_INK = [b for i in range(6) for b in (1, 0)] + [1]
# tables.QUAD_CLASSES order = X+,X-,Y+,Y-,Z+,Z-,PE+,PE-,PF+,PF-,PG+,PG-,N = region order here.
assert REG_NAME == tables.QUAD_CLASSES
EPS = 1e-9
TRIPLE_EDGES = {0: (E_, F_), 1: (E_, G_), 2: (F_, G_)}     # sealed cell -> the two kept old edges
TRIPLE_CLASS_NAMES = ["X'", "Y'", "Z'", "P1'", "P2'", "PK'"]


def cell_mass(x, y, z):
    return [x, y, z, 1 - x - y, 1 - x - z, 1 - y - z]


def region_mass(mass, kv):
    """kv = (k_X,k_Y,k_Z,k_PE,k_PF,k_PG,k_N) -> masses of the 13 regions."""
    out = []
    for i in range(6):
        out += [kv[i], mass[i] - kv[i]]
    return out + [kv[6]]


def present_regions(mass, d):
    P = []
    for r in range(12):
        c = REG_CELL[r]
        if mass[c] <= EPS: continue
        if REG_INK[r] and d[c] >= mass[c] - EPS: continue
        P.append(r)
    return frozenset(P + [12])


def sealed_cells(mass, d):
    return [c for c in range(3) if d[c] >= mass[c] - EPS]


def triple_class_map(c):
    """region -> class index (0..5) of the good triple (A1, A2, K) through sealed cell c, or None."""
    a1, a2 = TRIPLE_EDGES[c]
    code = {a1 | a2: 0, a1 | K_: 1, a2 | K_: 2, a1: 3, a2: 4, K_: 5, 0: None}
    out = []
    for r in range(NREG):
        tr = REG_MEM[r] & (a1 | a2 | K_)
        out.append(code.get(tr, "core"))
    return out


class Closure:
    """One closure type for a given (profile, D): table W[nT, nLam, nc] and aggregation matrix
    M[nc, 13] from region masses to class masses."""

    def __init__(self, name, r, pats, W, M, fast=None):
        self.name, self.r, self.pats, self.W, self.M = name, r, pats, W, M
        # fast: [list of pattern indices] (shared, mutable: grows when the full table finds a
        # better pattern); Wf = the corresponding sub-table
        self.fast = fast
        self.Wf = None if fast is None else np.ascontiguousarray(W[fast])

    def _sync(self):
        if self.fast is not None and len(self.fast) != len(self.Wf):
            self.Wf = np.ascontiguousarray(self.W[self.fast])

    def value(self, rm, full=False):
        """(value, pattern index).  full=False uses the fast sub-table (an upper bound on the
        true closure value, attained by a valid strategy)."""
        cm = self.M @ np.asarray(rm, float)
        if full or self.fast is None:
            v = (self.W @ cm).max(axis=1); i = int(v.argmin())
            if self.fast is not None and i not in self.fast: self.fast.append(i)
            return float(v[i]), i
        self._sync()
        v = (self.Wf @ cm).max(axis=1); i = int(v.argmin())
        return float(v[i]), self.fast[i]

    def best(self, rm, n=3):
        cm = self.M @ np.asarray(rm, float)
        if self.fast is None:
            v = (self.W @ cm).max(axis=1); idx = np.argsort(v)[:n]
            return [(float(v[i]), int(i)) for i in idx]
        self._sync()
        v = (self.Wf @ cm).max(axis=1); idx = np.argsort(v)[:n]
        return [(float(v[i]), self.fast[int(i)]) for i in idx]

    def rows(self, i):
        """region-level weight rows of pattern i (one per lambda), deduplicated, dominated removed."""
        R = self.W[i] @ self.M                      # [nLam, 13]
        R = np.unique(np.round(R, 12), axis=0)
        keep = []
        for a in range(len(R)):
            if not any(b != a and np.all(R[b] >= R[a] - 1e-12) and (np.any(R[b] > R[a] + 1e-12) or b < a)
                       for b in range(len(R))):
                keep.append(a)
        return R[keep]


FAST = os.environ.get("R1_FULL_TABLES", "") == ""
_fast = {}


def _fast_list(kind, key):
    if not FAST: return None
    if (kind, key) not in _fast: _fast[kind, key] = list(tables.fast_index(kind, key))
    return _fast[kind, key]


def closures(mass, d):
    """Closure types available to the requester for this (profile, D)."""
    P = present_regions(mass, d); sealed = sealed_cells(mass, d)
    sig = tuple(0 if mass[c] <= EPS else (1 if c in sealed else 2) for c in range(3))
    pats, W = tables.quad_table(sig)
    out = [Closure("Q", 3, pats, W, np.eye(NREG), _fast_list("quad", sig))]
    for c in sealed:
        cmap = triple_class_map(c)
        assert all(not (cmap[r] == "core" and r in P) for r in range(NREG))
        M = np.zeros((6, NREG))
        for r in range(NREG):
            if cmap[r] not in (None, "core"): M[cmap[r], r] = 1.0
        absent = tuple(j for j in range(3) if not any(cmap[r] == j and r in P for r in range(NREG)))
        pats, W = tables.triple_table(absent)
        out.append(Closure("T" + CELL_NAMES[c], 4, pats, W, M, _fast_list("triple", absent)))
    return out


def phi_static(x, y, z):
    """Optimal 4-request static closure of the good triple itself (honest on boundary faces)."""
    mass = cell_mass(x, y, z)
    absent = tuple(c for c in range(3) if mass[c] <= EPS)
    pats, W = tables.triple_table(absent)
    v = (W @ np.array(mass)).max(axis=1)
    i = int(v.argmin())
    return float(v[i]), pats[i]


def solver(time_limit=None):
    kw = dict(msg=False, threads=1)
    if time_limit: kw["timeLimit"] = time_limit
    return pulp.HiGHS(**kw)


# ------------------------------------------------------------------ adversary
class Rules:
    """What the adversary must respect.
    smax[c] (c = X,Y,Z): bound on S of the good triple formed by K and the two edges through
        cell c; it applies only when c is sealed.
    pairM: if not None, every pair intersection in the family is <= pairM or >= 1/2
        (the anchor pair E,F realizes the largest pair intersection that is <= k/2), so
        |K & A| <= pairM or >= 1/2 for A = E, F, G.  This needs no sealing."""

    def __init__(self, smax, pairM=None, smin=None, pot=None, pot0=None, half=False):
        self.smax = list(smax) if isinstance(smax, (list, tuple)) else [smax] * 3
        # smin: lower bound on S of every new good triple (anchor = good triple of MINIMUM S)
        self.smin = smin
        # pot = (al, be, ga): the anchor maximizes Phi = al*s1 + be*s2 + ga*s3 over all good
        # triples of the family, s1 >= s2 >= s3 the sorted pair cells; so every new good triple
        # has Phi' <= pot0 = Phi(anchor).  (1,1,1) is maxS, (-1,-1,-1) is minS.
        self.pot, self.pot0 = pot, pot0
        # half: the anchor is extremal only among good triples ALL of whose pair cells are <= 1/2
        # (the class in which the anchors of this experiment live), so a new good triple with a
        # pair cell > 1/2 is not constrained by the potential.
        self.half = half
        self.pairM = pairM if (pairM is not None and pairM < 0.5 - 1e-9) else None


def make_rules(variant, t, x, y, z):
    loose = 3 - 2 * t; S = x + y + z
    if variant == "none": return Rules(99.0)
    if variant == "loose": return Rules(loose)
    if variant == "maxS": return Rules(min(S, loose))
    if variant == "minS": return Rules(loose, smin=S)
    if variant.startswith("pot:") or variant.startswith("poth:"):
        al, be, ga = (float(v) for v in variant.split(":")[1].split(","))
        s1, s2, s3 = sorted((x, y, z), reverse=True)
        return Rules(loose, pot=(al, be, ga), pot0=al * s1 + be * s2 + ga * s3, half=variant.startswith("poth:"))
    if variant == "M": return Rules(loose, pairM=x)
    if variant == "MS":
        # anchor: pair with intersection M = x, and among good triples through such a pair max S
        mass = [x, y, z]
        return Rules([min(S, loose) if abs(mass[c] - x) < 1e-9 else loose for c in range(3)], pairM=x)
    raise ValueError(variant)


def edge_trace_coef(a):
    """coefficients over kv of |K & A| for an old edge A."""
    return [1 if CELL_MEM[i] & a else 0 for i in range(6)] + [0]


def looseness_rows(mass, d, rules):
    """list of (coef over kv[0..6], const, bound): const + coef.kv <= bound."""
    out = []
    for c in sealed_cells(mass, d):
        a1, a2 = TRIPLE_EDGES[c]
        coef = [u + v for u, v in zip(edge_trace_coef(a1), edge_trace_coef(a2))]
        out.append((coef, mass[c], rules.smax[c]))
        if rules.smin is not None:          # S' >= smin  <=>  -S' <= -smin
            out.append(([-a for a in coef], -mass[c], -rules.smin))
    return out


def potential_value(pot, cells):
    s1, s2, s3 = sorted(cells, reverse=True)
    return pot[0] * s1 + pot[1] * s2 + pot[2] * s3


def new_triple_cells(mass, c, kv):
    """pair cells of the good triple formed by K and the two edges through the sealed cell c."""
    a1, a2 = TRIPLE_EDGES[c]
    return (mass[c], sum(u * v for u, v in zip(edge_trace_coef(a1), kv)),
            sum(u * v for u, v in zip(edge_trace_coef(a2), kv)))


def admissible(mass, d, kv, rules, tol=1e-9, check_cap=True):
    """capacities are checked with tolerance tol, the rules with the looser RTOL (responses come
    from a floating-point MILP and may sit exactly on a rule boundary)."""
    if abs(sum(kv) - 1) > tol or min(kv) < -tol: return False
    if check_cap and any(kv[c] > mass[c] - d[c] + tol for c in range(6)): return False
    tol = RTOL
    if rules.pot is not None:
        for c in sealed_cells(mass, d):
            cells = new_triple_cells(mass, c, kv)
            if rules.half and max(cells) > 0.5 + tol: continue
            if potential_value(rules.pot, cells) > rules.pot0 + tol: return False
    for coef, const, bound in looseness_rows(mass, d, rules):
        if const + sum(a * b for a, b in zip(coef, kv)) > bound + tol: return False
    if rules.pairM is not None:
        for a in (E_, F_, G_):
            v = sum(u * w for u, w in zip(edge_trace_coef(a), kv))
            if rules.pairM + tol < v < 0.5 - tol: return False
    return True


MARG = 0.0          # no margin: the adversary may sit exactly on a rule boundary (closed sets)
RTOL = 2e-6          # float tolerance when re-checking the rules on a response found by the MILP


def adversary(mass, d, t, rules, pool, time_limit=120, kden=None, objective=None):
    """max mu s.t. K admissible and every pooled pattern (given as an array of region-weight
    rows) has some row with  row . rm(K) >= t + mu."""
    prob = pulp.LpProblem("adv", pulp.LpMaximize)
    if kden:      # responses on the grid of multiples of 1/kden
        nv = [prob.add_variable(f"n_{i}", 0, kden, cat="Integer") for i in range(7)]
        kv = [v * (1.0 / kden) for v in nv]
        prob += pulp.lpSum(nv) == kden
    else:
        nv = kv = [prob.add_variable(f"k_{i}", 0, 1) for i in range(7)]
        prob += pulp.lpSum(kv) == 1
    mu = prob.add_variable("mu", -1, 1)
    if objective is None: prob += mu
    else: prob += pulp.lpSum(float(a) * v for a, v in zip(objective, kv)) + 0 * mu      # used by check_wins_lp.py
    for c in range(6):
        prob += kv[c] <= max(mass[c] - d[c], 0.0) + 1e-9
    # rule constraints (closed; MARG = 0)
    for coef, const, bound in looseness_rows(mass, d, rules):
        prob += const + pulp.lpSum(a * v for a, v in zip(coef, kv) if a) <= bound - MARG
    if rules.pot is not None:
        al, be, ga = rules.pot
        for c in sealed_cells(mass, d):
            a1, a2 = TRIPLE_EDGES[c]
            va = pulp.lpSum(u * v for u, v in zip(edge_trace_coef(a1), kv) if u)
            vb = pulp.lpSum(u * v for u, v in zip(edge_trace_coef(a2), kv) if u)
            items = [("m", mass[c]), ("a", va), ("b", vb)]
            os_ = []
            for oi, perm in enumerate(itertools.permutations(range(3))):
                o = prob.add_variable(f"o_{c}_{oi}", cat="Binary"); os_.append(o)
                v1, v2, v3 = (items[i][1] for i in perm)
                prob += v1 - v2 >= -2.0 * (1 - o)
                prob += v2 - v3 >= -2.0 * (1 - o)
                prob += al * v1 + be * v2 + ga * v3 <= rules.pot0 - MARG + 8.0 * (1 - o)
            if rules.half and mass[c] <= 0.5 + EPS:
                # escape: one of the two new pair cells is > 1/2
                ea = prob.add_variable(f"ea_{c}", cat="Binary"); eb = prob.add_variable(f"eb_{c}", cat="Binary")
                prob += va >= (0.5 + 1e-5) * ea          # strictly more than half an edge
                prob += vb >= (0.5 + 1e-5) * eb
                prob += pulp.lpSum(os_) + ea + eb >= 1
                prob += pulp.lpSum(os_) <= 1
            elif rules.half:
                pass                                  # the sealed cell itself is > 1/2: no constraint
            else:
                prob += pulp.lpSum(os_) == 1
    if rules.pairM is not None:
        for a in (E_, F_, G_):
            h = prob.add_variable(f"h_{a}", cat="Binary")
            tr = pulp.lpSum(u * v for u, v in zip(edge_trace_coef(a), kv) if u)
            prob += tr <= rules.pairM + (1 - rules.pairM) * h
            prob += tr >= 0.5 * h
    rm = region_mass(mass, kv)
    BIG = 2.0
    for si, R in enumerate(pool):
        bs = [prob.add_variable(f"b_{si}_{j}", cat="Binary") for j in range(len(R))]
        prob += pulp.lpSum(bs) >= 1
        for j, row in enumerate(R):
            load = pulp.lpSum(float(row[reg]) * rm[reg] for reg in range(NREG) if row[reg] > 1e-12)
            prob += load >= t + mu - BIG * (1 - bs[j])
    st = prob.solve(solver(time_limit))
    if st.status.name == "Infeasible": return None, None
    if not st.has_solution:
        # rare HiGHS failure ("Undefined"): retry without presolve
        st = prob.solve(pulp.HiGHS(msg=False, threads=1, timeLimit=time_limit, presolve="off"))
        if st.status.name == "Infeasible": return None, None
        if not st.has_solution: raise RuntimeError(st.status.name)
    if kden:
        out = [round(v.value()) / kden for v in nv]
    else:
        # clamp to the capacities exactly and put the slack on new points
        out = [min(max(v.value(), 0.0), max(mass[c] - d[c], 0.0)) for c, v in enumerate(kv[:6])]
        tot = sum(out)
        if tot > 1.0: out = [v / tot for v in out]
        out.append(max(1.0 - sum(out), 0.0))
    return out, mu.value()


def closure_value(mass, d, kv, cls=None, stop_at=None, full=False):
    """min over closure types; if stop_at is given, return as soon as a value <= stop_at is found."""
    cls = cls or closures(mass, d)
    rm = region_mass(mass, kv)
    best = (9.0, None, None)
    for C in cls:
        v, i = C.value(rm, full)
        if v < best[0]: best = (v, C, i)
        if stop_at is not None and v <= stop_at: break
    return best


def play(mass, d, t, rules, seeds=(), tol=1e-6, max_iter=300, ncuts=3, kden=None):
    """One (profile, D).  Returns dict(result='R'|'A'|'U', ...).
    'R': the adversary MILP over the final pool has optimum mu <= tol (requester wins this D).
    'A': an admissible K whose exact-table closure value is > t + tol was found.
    'U': iteration cap reached."""
    cls = closures(mass, d)
    for kv in seeds:
        if admissible(mass, d, kv, rules):
            v, C, i = closure_value(mass, d, kv, cls, full=True)
            if v > t + tol: return dict(result="A", K=kv, value=v, iters=0)
    pool = []; pool_ids = []
    mu = None
    for it in range(max_iter):
        kv, mu = adversary(mass, d, t, rules, pool, kden=kden)
        if kv is None or mu <= tol:
            return dict(result="R", pool=pool_ids, mu=mu, iters=it)
        rm = region_mass(mass, kv)
        cands = []
        for C in cls:
            for v, i in C.best(rm, ncuts): cands.append((v, C, i))
        cands.sort(key=lambda a: a[0])
        if cands[0][0] > t + tol:
            # confirm with the full tables (this also adds the full optimum to the fast lists)
            for C in cls:
                v, i = C.value(rm, full=True); cands.append((v, C, i))
            cands.sort(key=lambda a: a[0])
            if cands[0][0] > t + tol:
                return dict(result="A", K=kv, value=cands[0][0], iters=it)
        added = 0
        for v, C, i in cands:
            if v <= t + tol and (C.name, i) not in pool_ids and added < ncuts:
                pool.append(C.rows(i)); pool_ids.append((C.name, i)); added += 1
        if not added:
            # numerical stalemate: K is beaten by a pooled pattern within tolerance
            return dict(result="R", pool=pool_ids, mu=mu, iters=it, note="stalemate")
    return dict(result="U", mu=mu, iters=max_iter)


# ------------------------------------------------------------------ request menu
def menu(mass, t, fine=False):
    """Finite menu of first requests D (vectors d over the six cells, sum = t)."""
    out = {}
    def add(d, tag):
        d = [min(max(v, 0.0), mass[i]) for i, v in enumerate(d)]
        if abs(sum(d) - t) > 1e-7: return
        key = tuple(round(v, 6) for v in d)
        out.setdefault(key, tag)
    # (1) priority orders: fill cells completely in a fixed order, last one partially
    for perm in itertools.permutations(range(6)):
        d = [0.0] * 6; rem = t
        for c in perm:
            a = min(mass[c], rem); d[c] = a; rem -= a
            if rem <= 1e-12: break
        add(d, "prio:" + ">".join(CELL_NAMES[c] for c in perm if d[c] > 0))
    # (2) seal a set of pair cells, spread the rest proportionally over a group of other cells
    for k in range(4):
        for sub in itertools.combinations(range(3), k):
            base = sum(mass[c] for c in sub)
            if base > t + 1e-12: continue
            rem0 = t - base
            others = [c for c in range(6) if c not in sub]
            groups = [g for n in range(2, len(others) + 1) for g in itertools.combinations(others, n)]
            for g in groups:
                tot = sum(mass[c] for c in g)
                if tot < rem0 - 1e-12 or tot <= 0: continue
                d = [0.0] * 6
                for c in sub: d[c] = mass[c]
                for c in g: d[c] = mass[c] * rem0 / tot
                add(d, "seal:" + "".join(CELL_NAMES[c] for c in sub) + "|prop:" + ",".join(CELL_NAMES[c] for c in g))
                if fine:
                    lo = rem0 / len(g)          # equal absolute amounts
                    if all(mass[c] >= lo for c in g):
                        d = [0.0] * 6
                        for c in sub: d[c] = mass[c]
                        for c in g: d[c] = lo
                        add(d, "seal:" + "".join(CELL_NAMES[c] for c in sub) + "|eq:" + ",".join(CELL_NAMES[c] for c in g))
    # order: more sealed cells first, then more total pair-cell mass in D
    items = sorted(out.items(), key=lambda kvp: (-sum(1 for c in range(3) if kvp[0][c] >= mass[c] - EPS),
                                                 -sum(kvp[0][:3])))
    return [(list(k), tag) for k, tag in items]


def value_profile(x, y, z, t, rules, tol=1e-6, max_iter=300, fine=False, verbose=False):
    """Requester's outcome at a profile.  Returns dict with 'win' in {'static','adaptive',None}."""
    mass = cell_mass(x, y, z)
    v0, s0 = phi_static(x, y, z)
    if v0 <= t + tol: return dict(win="static", phi=v0)
    seeds = []; losses = []; und = []
    for d, tag in menu(mass, t, fine):
        res = play(mass, d, t, rules, seeds=seeds, tol=tol, max_iter=max_iter)
        if verbose: print("   ", tag, res["result"], res.get("iters"), res.get("value"), flush=True)
        if res["result"] == "R":
            return dict(win="adaptive", phi=v0, D=d, tag=tag, pool=res["pool"], mu=res["mu"], iters=res["iters"])
        if res["result"] == "A":
            if res["K"] not in seeds: seeds.append(res["K"])
            losses.append((res["value"], d, tag, res["K"]))
        else:
            und.append((d, tag, res["mu"]))
    return dict(win=None, phi=v0, losses=losses, undecided=und)
