"""R1b: multi-round re-anchoring on top of the one-round engine of compute/r1.

Game (a sound restriction of the multi-round request game, see notes/R1b_RESULTS.md):
the anchor is a good triple with all pair cells <= 1/2 minimizing Phi = c*s1 + s2; put
v = Phi(anchor).  A position is a good triple q (all cells <= 1/2) together with the standing
hypothesis "every good triple of the class has Phi >= v".  From q the requester may
  * close statically (4 requests), or
  * make a request D; a response K then either contradicts the hypothesis, or is closed by
    3 static requests on the four edges / 4 static requests on a sealed new triple, or
  * (depth >= 2) the requester DROPS the edge opposite to a sealed cell c and continues from the
    new good triple q2 = (|c|, |K & A1|, |K & A2|) with depth - 1.
Dropping edges keeps the count at <= 7: (triple) + K + 3 static.  W(depth, v) = positions won.
The requester wins the family iff the anchor q is in W(depth, Phi(q)).

Implementation: game.adversary / game.admissible are replaced by versions that understand
rules.lookup (a callback deciding "q2 in W(depth-1, v)").  When a lookup is active the response
is restricted to multiples of 1/KDEN (restricted adversary: biases towards "win"); q2 is on the
1/KDEN grid while positions are on the coarser 1/PDEN grid, and q2 counts as won only if ALL
neighbouring grid positions (floor/ceil of the two new cells) are won.
"""
import os, sys, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r1"))
import pulp
import game
from game import (NREG, EPS, TRIPLE_EDGES, sealed_cells, edge_trace_coef, looseness_rows, region_mass, solver)

_orig_admissible = game.admissible


def traces(mass, c, kv):
    a1, a2 = TRIPLE_EDGES[c]
    return (sum(u * v for u, v in zip(edge_trace_coef(a1), kv)), sum(u * v for u, v in zip(edge_trace_coef(a2), kv)))


def admissible2(mass, d, kv, rules, tol=1e-9, check_cap=True):
    if not _orig_admissible(mass, d, kv, rules, tol, check_cap): return False
    gap = getattr(rules, "gap", None)
    if gap is not None:
        for e in (1, 2, 4):
            m = sum(u * v for u, v in zip(edge_trace_coef(e), kv))
            if gap[0] + 2e-6 < m < gap[1] - 2e-6: return False
    lb = getattr(rules, "lemB", None)
    if lb is not None and sum(kv[:6]) < lb - 2e-6: return False
    lk = getattr(rules, "lookup", None)
    if lk is None: return True
    kd = rules.kden
    for c in sealed_cells(mass, d):
        a, b = traces(mass, c, kv)
        i, j = round(a * kd), round(b * kd)
        if abs(i - a * kd) > 1e-6 or abs(j - b * kd) > 1e-6: return False      # off the response grid
        if lk(mass[c], i, j): return False
    return True


def adversary2(mass, d, t, rules, pool, time_limit=120, kden=None, objective=None):
    lk = getattr(rules, "lookup", None)
    if lk is not None: kden = rules.kden
    forb = getattr(rules, "forb", None)
    if lk is not None and forb is None: forb = rules.forb = {}
    while True:
        prob = pulp.LpProblem("adv", pulp.LpMaximize)
        if kden:
            nv = [prob.add_variable(f"n_{i}", 0, kden, cat="Integer") for i in range(7)]
            kv = [v * (1.0 / kden) for v in nv]
            prob += pulp.lpSum(nv) == kden
        else:
            nv = kv = [prob.add_variable(f"k_{i}", 0, 1) for i in range(7)]
            prob += pulp.lpSum(kv) == 1
        mu = prob.add_variable("mu", -1, 1)
        prob += mu
        for c in range(6):
            prob += kv[c] <= max(mass[c] - d[c], 0.0) + 1e-9
        for coef, const, bound in looseness_rows(mass, d, rules):
            prob += const + pulp.lpSum(a * v for a, v in zip(coef, kv) if a) <= bound
        sealed = sealed_cells(mass, d)
        if rules.pot is not None:
            al, be, ga = rules.pot
            # big-M for the potential rows: must exceed max(lhs) - pot0 over the whole box (cells in [0,1]).
            # (r1/game.py uses the constant 8, which is only valid for small weights: |a|+|b|+|c|+|pot0| <= 8.)
            BIGP = abs(al) + abs(be) + abs(ga) + abs(rules.pot0) + 1.0
            for c in sealed:
                a1, a2 = TRIPLE_EDGES[c]
                va = pulp.lpSum(u * v for u, v in zip(edge_trace_coef(a1), kv) if u)
                vb = pulp.lpSum(u * v for u, v in zip(edge_trace_coef(a2), kv) if u)
                items = [mass[c], va, vb]; os_ = []
                for oi, perm in enumerate(itertools.permutations(range(3))):
                    o = prob.add_variable(f"o_{c}_{oi}", cat="Binary"); os_.append(o)
                    v1, v2, v3 = (items[i] for i in perm)
                    prob += v1 - v2 >= -2.0 * (1 - o)
                    prob += v2 - v3 >= -2.0 * (1 - o)
                    prob += al * v1 + be * v2 + ga * v3 <= rules.pot0 + BIGP * (1 - o)
                if rules.half and mass[c] <= 0.5 + EPS:
                    ea = prob.add_variable(f"ea_{c}", cat="Binary"); eb = prob.add_variable(f"eb_{c}", cat="Binary")
                    prob += va >= (0.5 + 1e-5) * ea
                    prob += vb >= (0.5 + 1e-5) * eb
                    prob += pulp.lpSum(os_) + ea + eb >= 1
                    prob += pulp.lpSum(os_) <= 1
                elif not rules.half:
                    prob += pulp.lpSum(os_) == 1
        gap = getattr(rules, "gap", None)
        if gap is not None:          # pair gap: |K & A| <= gap[0] or >= gap[1] for every old edge A
            for e in (1, 2, 4):
                h = prob.add_variable(f"g_{e}", cat="Binary")
                tr = pulp.lpSum(u * v for u, v in zip(edge_trace_coef(e), kv) if u)
                prob += tr <= gap[0] + (1 - gap[0]) * h
                prob += tr >= gap[1] * h
        lb = getattr(rules, "lemB", None)
        if lb is not None:           # Lemma B: |K & (E u F u G)| >= (3t - |E u F u G|)/2
            prob += pulp.lpSum(kv[:6]) >= lb
        if lk is not None:
            for c in sealed:
                F = forb.get((c, round(mass[c] * 1e6)))
                if not F: continue
                a1, a2 = TRIPLE_EDGES[c]
                A = pulp.lpSum(u * v for u, v in zip(edge_trace_coef(a1), nv) if u)
                B = pulp.lpSum(u * v for u, v in zip(edge_trace_coef(a2), nv) if u)
                ind = {}
                for tag, X, vals in (("a", A, sorted({i for i, j in F})), ("b", B, sorted({j for i, j in F}))):
                    for i in vals:
                        z = prob.add_variable(f"z{tag}_{c}_{i}", cat="Binary")      # X == i
                        up = prob.add_variable(f"u{tag}_{c}_{i}", cat="Binary")     # X >= i + 1
                        lo = prob.add_variable(f"l{tag}_{c}_{i}", cat="Binary")     # X <= i - 1
                        prob += z + up + lo == 1
                        prob += X >= (i + 1) * up + i * z
                        prob += X <= (i - 1) * lo + i * z + kden * up
                        ind[tag, i] = z
                for (i, j) in F:
                    prob += ind["a", i] + ind["b", j] <= 1
        rm = region_mass(mass, kv)
        for si, R in enumerate(pool):
            bs = [prob.add_variable(f"b_{si}_{j}", cat="Binary") for j in range(len(R))]
            prob += pulp.lpSum(bs) >= 1
            for j, row in enumerate(R):
                load = pulp.lpSum(float(row[reg]) * rm[reg] for reg in range(NREG) if row[reg] > 1e-12)
                prob += load >= t + mu - 2.0 * (1 - bs[j])
        st = prob.solve(solver(time_limit))
        if st.status.name == "Infeasible": return None, None
        if not st.has_solution:
            st = prob.solve(pulp.HiGHS(msg=False, threads=1, timeLimit=time_limit, presolve="off"))
            if st.status.name == "Infeasible": return None, None
            if not st.has_solution: raise RuntimeError(st.status.name)
        if kden:
            out = [round(v.value()) / kden for v in nv]
        else:
            out = [min(max(v.value(), 0.0), max(mass[c] - d[c], 0.0)) for c, v in enumerate(kv[:6])]
            tot = sum(out)
            if tot > 1.0: out = [v / tot for v in out]
            out.append(max(1.0 - sum(out), 0.0))
        if lk is None or mu.value() <= 1e-6: return out, mu.value()
        # lazy re-anchoring cuts: is some sealed new triple a won position?
        new = False
        for c in sealed:
            a, b = traces(mass, c, out)
            i, j = round(a * kden), round(b * kden)
            if lk(mass[c], i, j):
                forb.setdefault((c, round(mass[c] * 1e6)), set()).add((i, j)); new = True
        if not new: return out, mu.value()


game.adversary = adversary2
game.admissible = admissible2
