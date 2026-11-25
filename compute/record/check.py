"""INDEPENDENT exact checker for the R1 record certificates (compute/record/certs/*.json).

Imports nothing from compute/r1, compute/r1b or the search code: it rebuilds every constraint,
every closure strategy and every load function from the definitions, and only multiplies the
stored rational multipliers out.  No LP is solved here.

What one certificate proves (continuum model, k = 1, budget t, potential C*s1 + s2, class all):
for every anchor profile p in  P = box & R,  R = {x >= y >= z >= 0, x + y <= 1, x + y + z <= 3 - 2t},
  * kind "static": the anchor triple itself is closed by 4 static requests (some pattern of
    the certificate has all loads <= t at p);
  * kind "plan": the request d(p) is valid (0 <= d_c <= |c|, sum <= t) and every response K
    admissible under (capacities, looseness, minimality of the anchor) is closed by Q or by a
    T_c with c sealed.
Facts used and NOT re-derived here (see notes/RECORD.md):
  (F1) a closure pattern (one family of labels per class, cross-intersecting on candidate
       pairs) with class masses m costs  max_{lam in simplex} sum_c m_c min_{L in F_c} lam(L)
       (LP duality), and this max is attained at a vertex of the arrangement
       {lam(A) = lam(B)} inside the simplex (concave piecewise-linear function); LAMBDA(r)
       below recomputes these vertices.
  (F2) the game semantics (sealing, the minimality and looseness rows), notes/RECORD.md sec. 1.
usage: py check.py CERTDIR_or_FILE ...
"""
import sys, os, json, gzip, itertools, functools
from fractions import Fraction as Fr

NV = 10                     # u = (x, y, z, kX, kY, kZ, kPE, kPF, kPG, kN)
E, F, G, K = 1, 2, 4, 8
MEM = [E | F, E | G, F | G, E, F, G]          # cells X, Y, Z, PE, PF, PG
NAMES = ["X", "Y", "Z", "PE", "PF", "PG"]
EDGES = {0: (E, F), 1: (E, G), 2: (F, G)}


class Bad(Exception): pass


def need(c, msg):
    if not c: raise Bad(msg)


# ---------------------------------------------------------------- affine functions
def A(d=None, k=0):
    v = [Fr(0)] * NV
    for i, a in (d or {}).items(): v[i] += Fr(a)
    return (tuple(v), Fr(k))


def comb(*terms):
    v = [Fr(0)] * NV; k = Fr(0)
    for (f, s) in terms:
        s = Fr(s)
        for i in range(NV): v[i] += s * f[0][i]
        k += s * f[1]
    return (tuple(v), k)


SIZE = [A({0: 1}), A({1: 1}), A({2: 1}), A({0: -1, 1: -1}, 1), A({0: -1, 2: -1}, 1), A({1: -1, 2: -1}, 1)]


def kv(c): return A({3 + c: 1})


def tr(edge): return comb(*[(kv(c), 1) for c in range(6) if MEM[c] & edge])


def leq(f, rhs):            # f <= rhs   ->  (coef, rhs')
    return (f[0], Fr(rhs) - f[1])


# ---------------------------------------------------------------- closure strategies
@functools.lru_cache(None)
def LAMBDA(r):
    hyp = set()
    for a in range(1 << r):
        for b in range(1 << r):
            if a & b or a == b: continue
            h = tuple((a >> j & 1) - (b >> j & 1) for j in range(r))
            hyp.add(h)
    hyp = sorted(hyp)
    pts = set()
    for S in itertools.combinations(hyp, r - 1):
        M = [[Fr(v) for v in h] + [Fr(0)] for h in S] + [[Fr(1)] * r + [Fr(1)]]
        sol = gauss(M, r)
        if sol is not None and all(v >= 0 for v in sol): pts.add(tuple(sol))
    return sorted(pts)


def gauss(M, n):
    M = [row[:] for row in M]
    for col in range(n):
        p = next((i for i in range(col, n) if M[i][col] != 0), None)
        if p is None: return None
        M[col], M[p] = M[p], M[col]
        pv = M[col][col]; M[col] = [v / pv for v in M[col]]
        for i in range(n):
            if i != col and M[i][col] != 0:
                f = M[i][col]; M[i] = [a - f * b for a, b in zip(M[i], M[col])]
    return [M[i][n] for i in range(n)]


def labels(fam, r):
    """family mask (bit L for label L, L a nonempty subset of [r]); -1 or 0 = no label."""
    if fam in (-1, 0): return []
    Ls = [L for L in range(1, 1 << r) if fam >> L & 1]
    need(fam >> (1 << r) == 0 and fam & 1 == 0, "bad family mask")
    return Ls


def weight(Ls, lam, r):
    if not Ls: return Fr(0)
    return min(sum(lam[j] for j in range(r) if L >> j & 1) for L in Ls)


class Strategy:
    """classes: list of (membership mask over the kept edges, mass affine fn, present?);
    full: mask of all kept edges; r: number of static requests."""

    def __init__(self, classes, full, r):
        self.classes, self.full, self.r = classes, full, r

    def rows(self, pat):
        need(len(pat) == len(self.classes), "pattern length")
        fams = [labels(f, self.r) for f in pat]
        for i, (mi, _, pi) in enumerate(self.classes):
            if not pi: continue
            for j, (mj, _, pj) in enumerate(self.classes):
                if j <= i or not pj or (mi | mj) != self.full: continue
                need(fams[i] and fams[j], "unlabelled class with a candidate partner")
                for L in fams[i]:
                    for M in fams[j]:
                        need(L & M, "candidate pair with disjoint labels")
            need(mi != self.full, "a class lies in every kept edge")
        out = []
        for lam in LAMBDA(self.r):
            out.append(comb(*[(m, weight(fams[i], lam, self.r)) for i, (_, m, p) in enumerate(self.classes) if p]))
        return out


def regions():
    """the 13 regions of E,F,G,K: (membership, mass, cell, inK)."""
    out = []
    for c in range(6):
        out.append((MEM[c] | K, kv(c), c, True))
        out.append((MEM[c], comb((SIZE[c], 1), (kv(c), -1)), c, False))
    out.append((K, kv(6), None, True))
    return out


def strategy(opt, sealed, absent=()):
    """absent: pair cells whose size is identically 0 on the polytope (checked by the caller):
    their points do not exist, so their classes impose nothing."""
    if opt == "S":
        return Strategy([(MEM[c], SIZE[c], c not in absent) for c in range(6)], E | F | G, 4)
    if opt == "Q":
        cl = [(m, f, not (inK and c in sealed) and c not in absent) for (m, f, c, inK) in regions()]
        return Strategy(cl, E | F | G | K, 3)
    need(opt[0] == "T", "unknown option")
    c = NAMES.index(opt[1:]); need(c in sealed, "T_c with c not sealed")
    a1, a2 = EDGES[c]; keep = a1 | a2 | K
    groups = {}
    for (m, f, cc, inK) in regions():
        mm = m & keep
        if mm == 0: continue
        if mm == keep:
            need(cc == c and inK, "core region"); continue       # c+ : empty, c is sealed
        groups.setdefault(mm, []).append(f)
    # class order of the certificate: (A1&A2, A1&K, A2&K, A1, A2, K)
    order = [a1 | a2, a1 | K, a2 | K, a1, a2, K]
    cl = [(mm, comb(*[(f, 1) for f in groups.get(mm, [])]), True) for mm in order]
    return Strategy(cl, keep, 4)


# ---------------------------------------------------------------- constraint systems
def profile_rows(t, box):
    R = {"R:yx": leq(A({1: 1, 0: -1}), 0), "R:zy": leq(A({2: 1, 1: -1}), 0), "R:z0": leq(A({2: -1}), 0),
         "R:xy1": leq(A({0: 1, 1: 1}), 1), "R:loose": leq(A({0: 1, 1: 1, 2: 1}), 3 - 2 * t)}
    for i, (lo, hi) in enumerate(box):
        R[f"B:{i}:lo"] = leq(A({i: -1}), -lo); R[f"B:{i}:hi"] = leq(A({i: 1}), hi)
    return R


def request(plan):
    sealed = [int(c) for c in plan["sealed"]]
    need(all(c in (0, 1, 2) for c in sealed), "sealed must be pair cells")
    d = []
    for c in range(6):
        if c in sealed: d.append(SIZE[c]); continue
        a, b = plan["req"].get(NAMES[c], ["0", ["0", "0", "0"]])
        d.append(A({0: Fr(b[0]), 1: Fr(b[1]), 2: Fr(b[2])}, Fr(a)))
    return sealed, d


def base_rows(plan, t):
    sealed, d = request(plan)
    R = {}
    for c in range(7): R[f"K:{c}:ge0"] = leq(comb((kv(c), -1)), 0)
    for c in range(6): R[f"K:{c}:cap"] = leq(comb((kv(c), 1), (SIZE[c], -1), (d[c], 1)), 0)
    tot = comb(*[(kv(c), 1) for c in range(7)])
    R["K:sum:hi"] = leq(tot, 1); R["K:sum:lo"] = leq(comb((tot, -1)), -1)
    for c in sealed:
        a1, a2 = EDGES[c]
        R[f"L:{c}"] = leq(comb((SIZE[c], 1), (tr(a1), 1), (tr(a2), 1)), 3 - 2 * t)
    return R


def branch_rows(plan, key):
    """key: list of (c, i, j): the branch  C*w_i + w_j >= C*x + y  for the new triple through c."""
    C = Fr(plan["C"]); R = {}
    for c, i, j in key:
        a1, a2 = EDGES[c]; w = [SIZE[c], tr(a1), tr(a2)]
        R[f"P:{c}:{i}{j}"] = leq(comb((A({0: C, 1: 1}), 1), (w[i], -C), (w[j], -1)), 0)
    return R


def combine(rows, y, strict=()):
    """sum y_name * row_name; returns (coef, rhs, strict weight)."""
    v = [Fr(0)] * NV; rhs = Fr(0); sw = Fr(0)
    for name, val in y.items():
        val = Fr(val); need(val >= 0, "negative multiplier")
        need(name in rows, "unknown row " + name)
        a, b = rows[name]
        for i in range(NV): v[i] += val * a[i]
        rhs += val * b
        if name in strict: sw += val
    return tuple(v), rhs, sw


def dual_ok(rows, y, f, bound):
    """y certifies  f <= bound  on {rows}."""
    v, rhs, _ = combine(rows, y)
    need(v == f[0], "dual: coefficients do not match")
    need(rhs + f[1] <= bound, "dual: bound fails")


def pert(y):
    """total multiplier on the rows whose right-hand side moves by <= 1/k at finite k
    (capacities after rounding the request down, the two looseness rows)."""
    return sum(Fr(v) for n, v in y.items() if n.endswith(":cap") or n.startswith("L:") or n == "R:loose")


class Walker:
    def __init__(self, t, strat_of):
        self.t, self.strat_of = t, strat_of; self.nodes = 0; self.leaves = 0
        self.Ycov = Fr(0); self.Ymot = Fr(0); self.k0 = Fr(0)     # rounding constants (RECORD sec. 4)

    def walk(self, node, rows, strict, depth):
        self.nodes += 1
        if "E" in node:
            v, rhs, sw = combine(rows, node["E"], strict)
            need(all(a == 0 for a in v), "empty: coefficients not zero")
            need(rhs < 0 or (rhs <= 0 and sw > 0), "empty: no contradiction")
            Y = pert(node["E"])
            if rhs < 0: self.k0 = max(self.k0, Y / -rhs)
            else: self.Ymot = max(self.Ymot, Y / sw)
            self.leaves += 1; return
        S = self.strat_of(node["opt"])
        fs = S.rows(node["pat"])
        ent = {}
        for key, e in node["rows"].items():
            li = int(e["lam"]); need(str(li) == key, "row key")
            ent[(fs[li][0], fs[li][1])] = e
        for f in fs:
            e = ent.get((f[0], f[1]))
            need(e is not None, "a load row of the pattern is not handled")
            if "y" in e:
                dual_ok(rows, e["y"], f, self.t); self.leaves += 1
                self.Ycov = max(self.Ycov, pert(e["y"]))
            else:
                nm = f"S:{depth}"
                need(nm not in rows, "strict row name clash")
                rows2 = dict(rows); rows2[nm] = (tuple(-a for a in f[0]), f[1] - self.t)
                self.walk(e["child"], rows2, strict | {nm}, depth + 1)


def load(fn):
    return json.load(gzip.open(fn, "rt")) if fn.endswith(".gz") else json.load(open(fn))


def check_cert(cert):
    t = Fr(cert["t"]); C = Fr(cert["C"]); need(C >= 1, "C >= 1 needed for the max form of the potential")
    box = [(Fr(a), Fr(b)) for a, b in cert["box"]]
    need(all(a <= b for a, b in box), "box")
    prof = profile_rows(t, box)
    if cert["kind"] == "outside":
        W = Walker(t, None); W.walk({"E": cert["E"]}, prof, frozenset(), 0); return W
    absent = [int(c) for c in (cert.get("absent") if cert["kind"] == "static" else cert.get("plan", {}).get("absent")) or []]
    for c in absent:
        need(c in (0, 1, 2) and box[c] == (0, 0), "absent cell must be identically empty on the box")
    if cert["kind"] == "static":
        S = strategy("S", [], absent)
        W = Walker(t, lambda opt: (need(opt == "S", "static option"), S)[1])
        W.walk(cert["roots"]["static"], prof, frozenset(), 0)
        return W
    need(cert["kind"] == "plan", "kind")
    plan = cert["plan"]; need(Fr(plan["t"]) == t and Fr(plan["C"]) == C, "plan t/C")
    sealed, d = request(plan)
    # validity of the request on P
    vrows = {}
    for c in range(6):
        if c in sealed: continue
        vrows[f"V:{NAMES[c]}:ge0"] = (comb((d[c], -1)), Fr(0))
        vrows[f"V:{NAMES[c]}:lecell"] = (comb((d[c], 1), (SIZE[c], -1)), Fr(0))
    vrows["V:budget"] = (comb(*[(d[c], 1) for c in range(6)]), t)
    for nm, (f, bound) in vrows.items():
        need(nm in cert["valid"], "validity row missing " + nm)
        dual_ok(prof, cert["valid"][nm], f, bound)
    base = dict(prof); base.update(base_rows(plan, t))
    strats = {}
    def strat_of(opt):
        if opt not in strats: strats[opt] = strategy(opt, sealed, absent)
        return strats[opt]
    W = Walker(t, strat_of)
    per = [[(c, i, j) for i, j in itertools.permutations(range(3), 2)] for c in sealed]
    for key in itertools.product(*per):
        k = json.dumps([list(x) for x in key])
        need(k in cert["roots"], "missing branch " + k)
        rows = dict(base); rows.update(branch_rows(plan, key))
        W.walk(cert["roots"][k], rows, frozenset(), 0)
    return W


# ---------------------------------------------------------------- cover of the profile region
def check_cover(index):
    """index: {"t","C","root":[[lo,hi]x3], "leaves": {path: certfile}}; path = string of octants
    '0'..'7' (bit i set = upper half in coordinate i).  The leaves must tile the root box."""
    root = [(Fr(a), Fr(b)) for a, b in index["root"]]
    need(root[0][0] <= 0 and root[0][1] >= 1 and root[1][0] <= 0 and root[1][1] >= Fr(1, 2)
         and root[2][0] <= 0 and root[2][1] >= Fr(1, 2), "root box must contain R")
    leaves = set(index["leaves"])
    def tiles(path):
        if path in leaves: return True
        need(len(path) < 40, "cover: path too deep / missing leaf under " + repr(path))
        return all(tiles(path + str(o)) for o in range(8))
    need(tiles(""), "cover")
    for p in leaves:
        need(not any(p[:i] in leaves for i in range(len(p))), "overlapping leaves")
    def box_of(path):
        b = list(root)
        for ch in path:
            o = int(ch); nb = []
            for i, (lo, hi) in enumerate(b):
                mid = (lo + hi) / 2
                nb.append((mid, hi) if o >> i & 1 else (lo, mid))
            b = nb
        return b
    return box_of


if __name__ == "__main__":
    tot = dict(files=0, nodes=0, leaves=0)
    for arg in sys.argv[1:]:
        if os.path.isdir(arg):
            idx = os.path.join(arg, "index.json")
            index = json.load(open(idx))
            box_of = check_cover(index)
            t, C = index["t"], index["C"]
            kinds = {}; R = dict(Ycov=Fr(0), Ymot=Fr(0), k0=Fr(0))
            for path, fn in sorted(index["leaves"].items()):
                cert = load(os.path.join(arg, fn))
                need(cert["t"] == t and cert["C"] == C, "t/C mismatch " + fn)
                need([(Fr(a), Fr(b)) for a, b in cert["box"]] == box_of(path), "box mismatch " + fn)
                W = check_cert(cert)
                kinds[cert["kind"]] = kinds.get(cert["kind"], 0) + 1
                tot["files"] += 1; tot["nodes"] += W.nodes; tot["leaves"] += W.leaves
                for kk in R: R[kk] = max(R[kk], getattr(W, kk))
            print(f"{arg}: COVER OK, t={t}, C={C}, {len(index['leaves'])} boxes {kinds}; "
                  f"{tot['nodes']} tree nodes, {tot['leaves']} exact leaf certificates; rounding: "
                  f"Ycov={float(R['Ycov']):.3f} Ymot={float(R['Ymot']):.3f} k0={float(R['k0']):.1f}")
        else:
            cert = load(arg)
            W = check_cert(cert)
            print(f"{arg}: OK ({cert['kind']}, box {cert['box']}, {W.nodes} nodes, {W.leaves} leaves, "
                  f"Ycov={float(W.Ycov):.3f} Ymot={float(W.Ymot):.3f} k0={float(W.k0):.1f})")
