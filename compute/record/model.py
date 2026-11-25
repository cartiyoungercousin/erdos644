"""Search-side model of the depth-1 sparsest-anchor game on a POLYTOPE of anchor profiles.

Continuum model, k = 1, budget t.  Joint variables
    u = (x, y, z, kX, kY, kZ, kPE, kPF, kPG, kN)          (n = 10)
x >= y >= z the sorted pair cells of the anchor E,F,G (X = E&F, Y = E&G, Z = F&G), privates
|PE| = 1-x-y, |PF| = 1-x-z, |PG| = 1-y-z; K = (kX..kPG, kN) the response (kN new points).

A *plan* fixes, for every anchor profile p of a polytope P (box & region R):
  * a set SIG of sealed pair cells, d_c(p) = |c|(p) for c in SIG;
  * an affine request d_c(p) = a_c + b_c . (x, y, z) on the other cells;  sum_c d_c(p) <= t on P.
Admissible responses (class 'all', anchor minimises Phi = C*s1 + s2 over ALL good triples):
  0 <= k_c <= |c| - d_c,  kN >= 0,  sum k = 1;
  for c in SIG, with a1 = |K & A1|, a2 = |K & A2| (A1, A2 the two anchor edges through c):
     looseness |c| + a1 + a2 <= 3 - 2t                         (Lean: goodTriple_S_le)
     minimality  max_{i != j} C*w_i + w_j >= C*x + y,  (w_0, w_1, w_2) = (|c|, a1, a2)
       -> one root polytope per choice of the ordered pair (i, j) for each sealed cell.
Closures (requester wins against K if one closure has all loads <= t):
  Q    : E,F,G,K + 3 static requests (quad table with sig 1 for sealed, 2 otherwise);
  T_c  : c in SIG, the good triple (A1, A2, K) + 4 static requests (triple table, nothing absent).
Every region is treated as present (also when its mass is 0 on part of P), except c+ for
sealed c: this is the conservative convention (a present class only adds constraints).
Static plan: phi(p) <= t on P (triple table on the anchor itself, nothing absent).

All constraints are kept as named rows  coef . u <= rhs  with Fraction data.
"""
from __future__ import annotations
import os, sys, itertools, functools
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "r1"))
import tables  # noqa: E402

N = 10
CELLS = ["X", "Y", "Z", "PE", "PF", "PG"]
E_, F_, G_, K_ = 1, 2, 4, 8
CELL_MEM = [E_ | F_, E_ | G_, F_ | G_, E_, F_, G_]
TRIPLE_EDGES = {0: (E_, F_), 1: (E_, G_), 2: (F_, G_)}


def lin(d=None, const=0):
    """affine function: (coef list of length N, const)."""
    c = [Fr(0)] * N
    for i, v in (d or {}).items(): c[i] = Fr(v)
    return (c, Fr(const))


def ladd(*fs):
    c = [Fr(0)] * N; k = Fr(0)
    for f, s in fs:
        for i in range(N): c[i] += s * f[0][i]
        k += s * f[1]
    return (c, k)


def cell_size(c):
    """|c| as an affine function of u."""
    return [lin({0: 1}), lin({1: 1}), lin({2: 1}),
            lin({0: -1, 1: -1}, 1), lin({0: -1, 2: -1}, 1), lin({1: -1, 2: -1}, 1)][c]


def kvar(c):           # c = 0..5 cells, 6 = new points
    return lin({3 + c: 1})


def trace(edge):
    """|K & A| for an anchor edge A."""
    return ladd(*[(kvar(c), 1) for c in range(6) if CELL_MEM[c] & edge])


def row(name, f, rhs):
    """constraint f(u) <= rhs  ->  (name, coef, rhs - const)."""
    return (name, list(f[0]), Fr(rhs) - f[1])


# ------------------------------------------------------------------ profile polytope
def profile_rows(t, box):
    """box = ((lox, hix), (loy, hiy), (loz, hiz)) with Fractions."""
    R = [row("R:yx", lin({1: 1, 0: -1}), 0), row("R:zy", lin({2: 1, 1: -1}), 0),
         row("R:z0", lin({2: -1}), 0), row("R:xy1", lin({0: 1, 1: 1}), 1),
         row("R:loose", lin({0: 1, 1: 1, 2: 1}), 3 - 2 * t)]
    for i, (lo, hi) in enumerate(box):
        R.append(row(f"B:{i}:lo", lin({i: -1}), -lo)); R.append(row(f"B:{i}:hi", lin({i: 1}), hi))
    return R


# ------------------------------------------------------------------ plans
class Plan:
    """sealed: tuple of pair cells; req: dict cell -> (a, (b0, b1, b2)) for the unsealed cells
    (cells not listed get 0)."""

    def __init__(self, sealed, req, C, t, absent=()):
        self.sealed = tuple(sorted(sealed)); self.req = dict(req); self.C = Fr(C); self.t = Fr(t)
        self.absent = tuple(sorted(absent))      # pair cells identically empty on the polytope

    def d(self, c):
        if c in self.sealed: return cell_size(c)
        a, b = self.req.get(c, (0, (0, 0, 0)))
        return lin({0: b[0], 1: b[1], 2: b[2]}, a)

    def validity_rows(self):
        """affine functions that must be <= bound on the profile polytope."""
        out = []
        for c in range(6):
            if c in self.sealed: continue
            out.append((f"V:{CELLS[c]}:ge0", ladd((self.d(c), -1)), Fr(0)))
            out.append((f"V:{CELLS[c]}:lecell", ladd((self.d(c), 1), (cell_size(c), -1)), Fr(0)))
        out.append(("V:budget", ladd(*[(self.d(c), 1) for c in range(6)]), self.t))
        return out

    def base_rows(self):
        t = self.t
        out = []
        for c in range(7):
            out.append(row(f"K:{c}:ge0", ladd((kvar(c), -1)), 0))
        for c in range(6):
            out.append(row(f"K:{c}:cap", ladd((kvar(c), 1), (cell_size(c), -1), (self.d(c), 1)), 0))
        tot = ladd(*[(kvar(c), 1) for c in range(7)])
        out.append(row("K:sum:hi", tot, 1)); out.append(row("K:sum:lo", ladd((tot, -1)), -1))
        for c in self.sealed:
            a1, a2 = TRIPLE_EDGES[c]
            out.append(row(f"L:{c}", ladd((cell_size(c), 1), (trace(a1), 1), (trace(a2), 1)), 3 - 2 * t))
        return out

    def branches(self):
        """list of (key, rows): one per choice of ordered pair (i, j) per sealed cell."""
        per = []
        for c in self.sealed:
            a1, a2 = TRIPLE_EDGES[c]
            w = [cell_size(c), trace(a1), trace(a2)]
            v = lin({0: self.C, 1: 1})
            opts = []
            for i, j in itertools.permutations(range(3), 2):
                # C*w_i + w_j >= C*x + y   <=>   v - C*w_i - w_j <= 0
                opts.append(((c, i, j), row(f"P:{c}:{i}{j}", ladd((v, 1), (w[i], -self.C), (w[j], -1)), 0)))
            per.append(opts)
        out = []
        for combo in itertools.product(*per):
            out.append((tuple(k for k, _ in combo), [r for _, r in combo]))
        return out

    def to_json(self):
        return dict(sealed=list(self.sealed), req={CELLS[c]: [str(a), [str(v) for v in b]] for c, (a, b) in self.req.items()},
                    C=str(self.C), t=str(self.t), absent=list(self.absent))


# ------------------------------------------------------------------ closures as affine rows
def region_affine():
    """13 region masses (order of tables.QUAD_CLASSES) as affine functions of u."""
    out = []
    for c in range(6):
        out.append(kvar(c)); out.append(ladd((cell_size(c), 1), (kvar(c), -1)))
    out.append(kvar(6))
    return out


def triple_class_map(c):
    a1, a2 = TRIPLE_EDGES[c]
    code = {a1 | a2: 0, a1 | K_: 1, a2 | K_: 2, a1: 3, a2: 4, K_: 5, 0: None}
    mem = [CELL_MEM[i] | (K_ if b else 0) for i in range(6) for b in (1, 0)] + [K_]
    return [code.get(m & (a1 | a2 | K_), "core") for m in mem]


def to_np(fs):
    A = np.array([[float(v) for v in f[0]] for f in fs]); b = np.array([float(f[1]) for f in fs])
    return A, b


class Option:
    """one closure type: patterns (family tuples), float weights W[pat, lam, cls], and the affine
    class-mass map (Mc: cls x N, m0: cls)."""

    def __init__(self, name, r, kind, key, pats, W, cls_aff):
        self.name, self.r, self.kind, self.key, self.pats, self.W = name, r, kind, key, pats, W
        self.cls_aff = cls_aff
        self.Mc, self.m0 = to_np(cls_aff)
        self._rows = {}

    def values(self, U):
        """U: s x N sample points -> P x s closure values (max over lambda)."""
        CM = U @ self.Mc.T + self.m0             # s x cls
        V = np.einsum("plc,sc->pls", self.W, CM, optimize=True)
        return V.max(axis=1)

    def rows(self, i):
        """exact affine load functions of pattern i, deduplicated (list of (coef, const), lam idx)."""
        if i in self._rows: return self._rows[i]
        Wx = tables.exact_weights(self.r, self.pats[i])       # lam x cls Fractions
        seen = {}
        for li, wl in enumerate(Wx):
            f = ladd(*[(self.cls_aff[c], w) for c, w in enumerate(wl) if w != 0]) if any(wl) else lin()
            key = (tuple(f[0]), f[1])
            if key not in seen: seen[key] = (f, li)
        out = list(seen.values())
        # drop rows dominated as functions? (only exact duplicates removed: domination depends on P)
        self._rows[i] = out
        return out


@functools.lru_cache(None)
def _quad(sig):
    return tables.quad_table(sig)


@functools.lru_cache(None)
def _triple():
    return tables.triple_table(())


def options_for(plan):
    sig = tuple(0 if c in plan.absent else (1 if c in plan.sealed else 2) for c in range(3))
    pats, W = _quad(sig)
    out = [Option("Q", 3, "quad", sig, pats, W, region_affine())]
    for c in plan.sealed:
        cm = triple_class_map(c)
        reg = region_affine()
        cls = []
        for j in range(6):
            cls.append(ladd(*[(reg[r], 1) for r in range(13) if cm[r] == j]))
        for r in range(13):
            # the core region (in A1, A2 and K) is c+ itself, which is sealed (mass 0)
            assert cm[r] != "core" or r == 2 * c
        pats, W = _triple()
        out.append(Option("T" + CELLS[c], 4, "triple", (), pats, W, cls))
    return out


def static_option(absent=()):
    pats, W = tables.triple_table(tuple(absent))
    return Option("S", 4, "triple", tuple(absent), pats, W, [cell_size(c) for c in range(6)])
