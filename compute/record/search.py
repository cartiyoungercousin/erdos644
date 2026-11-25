"""Certificate search: for a plan on a profile polytope, build a proof tree that every admissible
(profile, response) pair is closed.  Decisions use floating-point LPs (scipy/HiGHS); every leaf
is backed by an EXACT rational certificate (exact_lp), re-verified later by check.py.

Tree semantics (node = polytope N: named non-strict rows plus strict rows from the path):
  EMPTY  : y >= 0 with sum_i y_i a_i = 0 and  y.b < 0, or (y.b <= 0 and y > 0 on a strict row)
           (Farkas / Motzkin): N is empty.
  PATTERN (option, pattern): for every load row l of the pattern either a dual certificate
           y >= 0, sum y_i a_i = w_l, y.b + w0_l <= t   (l <= t on the closure of N), or a child
           node N & {l > t}.  Then N is contained in {pattern closes} u (children).
"""
from __future__ import annotations
import os, time
import numpy as np
from fractions import Fraction as Fr
from scipy.optimize import linprog
import model, tables
from exact_lp import feasible_std

TOL = 1e-9


class Fail(Exception):
    def __init__(self, msg, u=None):
        super().__init__(msg); self.u = u


def fstr(v): return str(v)


class Searcher:
    def __init__(self, t, options, n=model.N, max_nodes=4000, max_depth=int(os.environ.get("REC_DEPTH", "10")), fast=True, nsamp=None):
        self.t = Fr(t); self.tf = float(t); self.opts = options; self.n = n
        self.max_nodes, self.max_depth = max_nodes, max_depth
        self.nodes = 0
        self.nsamp = nsamp or (n + 4)
        self.rng = np.random.default_rng(0)
        # fast sub-tables: candidate pattern indices per option
        self.fast = []
        for o in options:
            fl = tables.fast_index(o.kind, tuple(o.key)) if fast else list(range(len(o.pats)))
            self.fast.append(np.array(fl, dtype=int))
        self.stats = dict(lp=0, exact=0, exact_fail=0)
        self.static = len(options) == 1 and options[0].name == "S"

    # ------------------------------------------------------------- LP helpers
    def _arr(self, rows):
        A = np.array([[float(v) for v in r[1]] for r in rows]); b = np.array([float(r[2]) for r in rows])
        return A, b

    def lp_max(self, A, b, w):
        self.stats["lp"] += 1
        res = linprog(-w, A_ub=A, b_ub=b, bounds=[(None, None)] * self.n, method="highs")
        if res.status == 2: return None, None
        if res.status == 3: return np.inf, None
        if res.status != 0: raise Fail("lp status %d" % res.status)
        return -res.fun, res.x

    def emptiness(self, A, b, strict):
        """max s: A u <= b (non-strict rows), A u + s <= b (strict rows), s <= 1."""
        self.stats["lp"] += 1
        m = len(b)
        Aext = np.hstack([A, np.array(strict, float)[:, None]])
        c = np.zeros(self.n + 1); c[-1] = -1
        res = linprog(c, A_ub=Aext, b_ub=b, bounds=[(None, None)] * self.n + [(None, 1)], method="highs")
        if res.status == 2: return None, None
        if res.status != 0: raise Fail("empt lp status %d" % res.status)
        return -res.fun, res.x[:-1]

    # ------------------------------------------------------------- exact certificates
    def cert(self, rows, target, bound, strict_norm=False, Af=None, bf=None):
        """find y >= 0 with sum y_i coef_i = target and y.rhs <= bound (exact), via float support.
        strict_norm: additionally sum of y over strict rows = 1 (Motzkin).  Returns {name: y} or None."""
        self.stats["exact"] += 1
        m = len(rows); n = self.n
        M = [[rows[i][1][j] for i in range(m)] + [Fr(0)] for j in range(n)]
        r = list(target)
        # bound row: rhs.y + slack = bound
        M.append([rows[i][2] for i in range(m)] + [Fr(1)]); r.append(Fr(bound))
        if strict_norm:
            M.append([Fr(1) if rows[i][3] else Fr(0) for i in range(m)] + [Fr(0)]); r.append(Fr(1))
        # float guess of the support
        cols = None
        try:
            Mf = np.array([[float(v) for v in rr] for rr in M]); rf = np.array([float(v) for v in r])
            res = linprog(np.r_[np.ones(m), 0.0], A_eq=Mf, b_eq=rf, bounds=[(0, None)] * (m + 1), method="highs")
            if res.status == 0:
                cols = [j for j in range(m + 1) if res.x[j] > 1e-11]
                if m not in cols: cols.append(m)
        except Exception:
            cols = None
        y = feasible_std(M, r, cols) if cols is not None else None
        if y is None:
            y = feasible_std(M, r)
        if y is None:
            self.stats["exact_fail"] += 1; return None
        return {rows[i][0]: fstr(y[i]) for i in range(m) if y[i] != 0}

    def cert_empty(self, rows):
        zero = [Fr(0)] * self.n
        y = self.cert(rows, zero, Fr(-1))
        if y is not None: return y
        if any(r[3] for r in rows):
            return self.cert(rows, zero, Fr(0), strict_norm=True)
        return None

    # ------------------------------------------------------------- search
    def solve_root(self, rows):
        """rows: list of (name, coef, rhs) non-strict.  Returns a certificate tree or raises Fail."""
        rows = [(nm, c, r, False) for nm, c, r in rows]
        return self.node(rows, 0, frozenset())

    def samples(self, A, b, u0):
        pts = [u0]
        for _ in range(self.nsamp):
            w = self.rng.normal(size=self.n)
            if self.static: w[3:] = 0
            v, x = self.lp_max(A, b, w)
            if x is not None: pts.append(x)
        return pts

    def node(self, rows, depth, used):
        self.nodes += 1
        if self.nodes > self.max_nodes: raise Fail("node limit")
        A, b = self._arr(rows)
        strict = [1.0 if r[3] else 0.0 for r in rows]
        s, u0 = self.emptiness(A, b, strict)
        if s is None or s <= TOL:
            y = self.cert_empty(rows)
            if y is not None: return {"E": y}
            if s is None: raise Fail("empty but no exact certificate")
        if depth > self.max_depth: raise Fail("depth limit", u0)
        pts = self.samples(A, b, u0)
        # rank patterns of every option by their worst value over the sample points
        cands = []
        U = np.array(pts)
        for oi, o in enumerate(self.opts):
            V = o.values(U)                             # P x s
            mx = V.max(axis=1)
            for (uo, ui) in used:
                if uo == oi: mx[ui] = np.inf
            idx = np.argsort(mx)[:6]
            for i in idx:
                if np.isfinite(mx[i]): cands.append((float(mx[i]), float(V[i, 0]), oi, int(i)))
        cands.sort()
        best_at_u0 = min(c[1] for c in cands)
        if best_at_u0 > self.tf + 1e-7:
            # nothing in the full tables either?
            full = min(float(o.values(U[:1]).min()) for o in self.opts)
            if full > self.tf + 1e-7: raise Fail("adversary point (value %.6f)" % full, u0)
        tried = []
        for mx, v0, oi, i in cands[:8]:
            o = self.opts[oi]
            viol, certs = self.check_pattern(rows, A, b, o, i)
            if not viol:
                return {"opt": o.name, "pat": list(o.pats[i]), "rows": certs}
            tried.append((len(viol), mx, oi, i, viol, certs))
            if v0 > self.tf + 1e-7: continue
        # split on the pattern with the fewest violated rows among those that close u0
        good = [z for z in tried if self.opts[z[2]].values(U[:1])[z[3], 0] <= self.tf + 1e-7]
        if not good: good = tried
        good.sort(key=lambda z: (z[0], z[1]))
        nv, mx, oi, i, viol, certs = good[0]
        o = self.opts[oi]
        out = dict(certs)
        for key, (f, li) in viol.items():
            # child: N & {f > t}  i.e.  -f.u < f0 - t
            # f.u + f0 > t   <=>   -f.u < f0 - t
            srow = (f"S:{depth}", [-v for v in f[0]], f[1] - self.t, True)
            child = self.node(rows + [srow], depth + 1, used | {(oi, i)})
            out[key] = {"lam": li, "child": child}
        return {"opt": o.name, "pat": list(o.pats[i]), "rows": out}

    def check_pattern(self, rows, A, b, o, i):
        """returns (violated rows {key: (f, lam)}, certs {key: {lam, y}})."""
        viol = {}; certs = {}
        for f, li in o.rows(i):
            key = str(li)
            w = np.array([float(v) for v in f[0]]); w0 = float(f[1])
            v, x = self.lp_max(A, b, w)
            if v is None: v = -np.inf
            if v + w0 <= self.tf + TOL:
                y = self.cert(rows, f[0], self.t - f[1])
                if y is not None:
                    certs[key] = {"lam": li, "y": y}; continue
            viol[key] = (f, li)
        return viol, certs


def count_nodes(tr):
    if "E" in tr: return 1
    return 1 + sum(count_nodes(v["child"]) for v in tr["rows"].values() if "child" in v)
