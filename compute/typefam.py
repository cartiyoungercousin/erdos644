"""Block-type families and the (p,2) property, via the Venn-signature ILP.

A *block-type family* is given by
  * a partition of the ground set into blocks V_0, ..., V_{m-1} with sizes `sizes`, and
  * a set of allowed *types* c = (c_0, ..., c_{m-1}) with sum(c) = r:
    the family is ALL r-sets A with (|A ∩ V_0|, ..., |A ∩ V_{m-1}|) an allowed type.
Examples: complete r-graph on n points = one block, type (r,);
FKW parity family = blocks X (4k), Y (3k+1), types with c_X odd.

Key facts used (see notes/LITERATURE.md, "signature view"):
  * For sets A_1..A_p let sig(x) = {i : x in A_i}. Then tau(A_1..A_p) <= 2 iff some point has
    sig = [p], or two points have sig(x) | sig(y) = [p].
  * A p-tuple (repetitions allowed) of edges is described by counts m[b][s] = number of points
    of block b with signature s. Edge i has type (sum_{s ∋ i} m[b][s])_b.
  * Repetitions are harmless: if the family has >= p edges, a bad tuple with repeats extends to a
    bad p-set of distinct edges (adding edges never lowers tau).
  * tau of the family only depends on t_b = |T ∩ V_b|: T is a transversal iff no allowed type c
    satisfies c_b <= sizes[b] - t_b for all b.
"""
from __future__ import annotations

import itertools
from dataclasses import dataclass, field

import pulp


def compositions_bounded(total: int, bounds: list[int]):
    """All tuples c with 0 <= c_b <= bounds[b] and sum c = total."""
    if not bounds:
        if total == 0:
            yield ()
        return
    first, rest = bounds[0], bounds[1:]
    rest_cap = sum(rest)
    for c0 in range(max(0, total - rest_cap), min(first, total) + 1):
        for tail in compositions_bounded(total - c0, rest):
            yield (c0,) + tail


@dataclass
class TypeFamily:
    sizes: list[int]
    types: list[tuple[int, ...]]
    name: str = ""
    r: int = field(init=False)

    def __post_init__(self):
        self.types = sorted(set(self.types))
        if not self.types:
            raise ValueError("empty family")
        rs = {sum(c) for c in self.types}
        if len(rs) != 1:
            raise ValueError(f"types must all have the same total, got {rs}")
        self.r = rs.pop()
        for c in self.types:
            assert all(0 <= cb <= sb for cb, sb in zip(c, self.sizes)), c

    @classmethod
    def from_predicate(cls, sizes, r, pred, name=""):
        return cls(list(sizes), [c for c in compositions_bounded(r, list(sizes)) if pred(c)], name)

    @property
    def n(self) -> int:
        return sum(self.sizes)

    # ------------------------------------------------------------------ tau
    def tau(self) -> tuple[int, tuple[int, ...]]:
        """Exact transversal number and an optimal (t_b) vector."""
        m = len(self.sizes)
        # a vector t is a transversal iff every type c has some b with c_b > sizes[b]-t_b,
        # i.e. t_b >= sizes[b] - c_b + 1 for some b.
        for total in range(0, self.n + 1):
            for t in compositions_bounded(total, self.sizes):
                if all(any(t[b] >= self.sizes[b] - c[b] + 1 for b in range(m)) for c in self.types):
                    return total, t
        raise RuntimeError("unreachable")

    # ------------------------------------------------------- bad p-tuples
    def find_bad_tuple(self, p: int = 7, time_limit: float | None = None, msg: bool = False):
        """Search for p edges with no 2-point transversal.

        Returns None if none exists (property (p,2) holds), else a dict describing the witness:
        {'m': {(b, sig): count}, 'edge_types': [type of edge i]}.
        """
        m_blocks = len(self.sizes)
        full = (1 << p) - 1
        sigs = range(1 << p)
        prob = pulp.LpProblem("bad_tuple", pulp.LpMinimize)
        mv = {(b, s): prob.add_variable(f"m_{b}_{s}", 0, self.sizes[b], cat="Integer")
              for b in range(m_blocks) for s in sigs}
        z = {s: prob.add_variable(f"z_{s}", cat="Binary") for s in sigs}
        for b in range(m_blocks):
            prob += pulp.lpSum(mv[b, s] for s in sigs) == self.sizes[b]
            for s in sigs:
                prob += mv[b, s] <= self.sizes[b] * z[s]
        prob += z[full] == 0
        for s in sigs:
            for s2 in sigs:
                if s < s2 and (s | s2) == full:
                    prob += z[s] + z[s2] <= 1
        # each edge picks an allowed type
        y = {}
        for i in range(p):
            for j, c in enumerate(self.types):
                y[i, j] = prob.add_variable(f"y_{i}_{j}", cat="Binary")
            prob += pulp.lpSum(y[i, j] for j in range(len(self.types))) == 1
            for b in range(m_blocks):
                prob += (pulp.lpSum(mv[b, s] for s in sigs if s >> i & 1)
                         == pulp.lpSum(c[b] * y[i, j] for j, c in enumerate(self.types)))
        # symmetry breaking: edge types in nondecreasing index order
        idx = [pulp.lpSum(j * y[i, j] for j in range(len(self.types))) for i in range(p)]
        for i in range(p - 1):
            prob += idx[i] <= idx[i + 1]
        solver = pulp.HiGHS(msg=msg, timeLimit=time_limit) if time_limit else pulp.HiGHS(msg=msg)
        stats = prob.solve(solver)
        st = stats.status.name
        if st == "Infeasible":
            return None
        if st != "Optimal" or not stats.has_solution:
            raise RuntimeError(f"solver status {st}")
        witness = {(b, s): int(round(mv[b, s].value())) for b in range(m_blocks) for s in sigs
                   if round(mv[b, s].value()) > 0}
        types = [self.types[j] for i in range(p) for j in range(len(self.types))
                 if round(y[i, j].value()) == 1]
        return {"m": witness, "edge_types": types}


# ---------------------------------------------------------------- witnesses
def verify_witness(fam: TypeFamily, w: dict, p: int = 7) -> bool:
    """Independently rebuild the p sets from a witness and brute-force check tau >= 3."""
    pts = []  # (block, signature)
    for (b, s), cnt in w["m"].items():
        pts += [(b, s)] * cnt
    if [sum(1 for (b, _) in pts if b == bb) for bb in range(len(fam.sizes))] != fam.sizes:
        return False
    sets = [frozenset(k for k, (_, s) in enumerate(pts) if s >> i & 1) for i in range(p)]
    for i, A in enumerate(sets):
        typ = tuple(sum(1 for k in A if pts[k][0] == b) for b in range(len(fam.sizes)))
        if typ not in fam.types:
            return False
    n = len(pts)
    for x in range(n):
        for y in range(x, n):
            if all(x in A or y in A for A in sets):
                return False
    return True


# ---------------------------------------------------------------- examples
def complete(n: int, r: int) -> TypeFamily:
    return TypeFamily([n], [(r,)], name=f"K_{n}^({r})")


def parity(k: int, extra: int = 1) -> TypeFamily:
    """FKW family: |X| = 4k, |Y| = 3k+extra, all 4k-sets meeting X in an odd number."""
    return TypeFamily.from_predicate([4 * k, 3 * k + extra], 4 * k, lambda c: c[0] % 2 == 1,
                                     name=f"parity(k={k})")
