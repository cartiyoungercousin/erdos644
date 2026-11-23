"""R1b "star" continuation: purely adaptive play, no static phase.

Named edges: 0,1,2 = the anchor good triple E,F,G (cells x,y,z), then responses 3..n-1 (n <= 7).
The requester wins if the n named edges have no 2-point cover.  In the k -> infinity cell model
with an adversary who may place O(1) points anywhere he is allowed to, a Venn cell sigma (set of
named edges containing the point) is ABSENT only if it was sealed: for some response j in sigma
the whole parent cell sigma & [<j] was inside the request D_j (or its anchor cell is empty).
A 2-cover exists iff two present cells have union [n].  So the requester needs a *seal plan*
    s_j(tau) in {0,1},  j = 3..n-1,  tau a non-empty cell of the edges [<j]
that (i) kills one cell of every covering pair, and (ii) is affordable.  Requests may also take
a FRACTION g_j(tau)/Q of a cell (sealed = the whole cell); response j then gets at most the rest
of that cell.  Affordable: in every round j the request size sum_tau (g_j(tau)/Q) * mass(tau) is
<= t whatever the earlier responses were.

Restriction (biases toward "stuck"): the plan (fractions per cell TYPE and round) is fixed in
advance; the real requester could choose amounts after seeing the cell sizes.  The adversary is unrestricted (any responses of
size 1 respecting the seals, new points free; no looseness / gap / Lemma B rows by default).

Search: master binary program over plans (completeness constraints + cuts), adversary LP per
round (max mass of the cells to be sealed in round j over all consistent earlier responses).
Cut from an adversary play m*: either the new plan seals, in an earlier round, a cell that m*'s
response uses, or the round-j seal mass at m* is <= t.

usage: py star.py x y z t [n=7] [--loose]     (floating-point LP/MILP: evidence only)
"""
import os, sys, itertools, math
Q = 8          # requests take multiples of 1/Q of each cell
NOTRACE = False   # diagnostic only (UNSOUND as a rule): responses never meet the centre G
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "r1"))
from fractions import Fraction
import pulp
import game


def anchor_cells(x, y, z):
    # bit 0 = E, 1 = F, 2 = G
    return {0b011: x, 0b101: y, 0b110: z, 0b001: 1 - x - y, 0b010: 1 - x - z, 0b100: 1 - y - z, 0b111: 0.0}


def possible(tau, anc):
    """can a cell with this pattern be non-empty at all (anchor restriction)?"""
    p = tau & 7
    if NOTRACE and (tau & 4) and (tau >> 3): return False     # diagnostic: no response meets G
    return p == 0 or anc[p] > 1e-12


def adversary_lp(j, plan, anc, t, loose=None):
    """max total mass of the cells sealed by plan in round j, over all plays of rounds < j."""
    cells = [tau for tau in range(1, 1 << j) if possible(tau, anc)]
    prob = pulp.LpProblem("adv", pulp.LpMaximize)
    m = {tau: prob.add_variable(f"m_{tau}", 0, 1) for tau in cells}
    prob += pulp.lpSum(plan[j][tau] * m[tau] for tau in cells if plan[j].get(tau)) + 0 * m[cells[0]]
    for p in range(1, 7):
        prob += pulp.lpSum(m[tau] for tau in cells if tau & 7 == p) == anc[p]
    for i in range(3, j):
        prob += pulp.lpSum(m[tau] for tau in cells if (tau >> i) & 1) == 1
        low = (1 << i) - 1
        for par, f in plan[i].items():          # response i takes at most (1 - f) of its parent cell
            if f >= 1 - 1e-12:
                for tau in cells:
                    if (tau >> i) & 1 and tau & low == par: prob += m[tau] == 0
            elif f > 0:
                inp = [m[tau] for tau in cells if tau < (1 << (i + 1)) or True if (tau >> i) & 1 and tau & low == par]
                allp = [m[tau] for tau in cells if tau & low == par]
                prob += pulp.lpSum(inp) <= (1 - f) * pulp.lpSum(allp)
    if loose is not None:
        # tight-triple lemma for good triples (a, b, i) made good by a seal is not encoded; only
        # the cheap global consequence |union of any good anchor triple| is already fixed.
        pass
    st = prob.solve(game.solver())
    if st.status.name != "Optimal": return None, None
    val = sum(plan[j][tau] * m[tau].value() for tau in cells if plan[j].get(tau))
    return val, {tau: m[tau].value() for tau in cells if m[tau].value() > 1e-9}


def solve(x, y, z, t, n=7, max_iter=3000, verbose=False):
    anc = anchor_cells(x, y, z)
    full = (1 << n) - 1
    cells = [s for s in range(1, 1 << n) if possible(s, anc)]
    def keys(s):          # seal variables that kill cell s
        return [(j, s & ((1 << j) - 1)) for j in range(3, n) if (s >> j) & 1 and s & ((1 << j) - 1)]
    prob = pulp.LpProblem("plan", pulp.LpMinimize)
    S = {}; Gv = {}
    for j in range(3, n):
        for tau in range(1, 1 << j):
            if possible(tau, anc):
                S[j, tau] = prob.add_variable(f"s_{j}_{tau}", cat="Binary")            # cell sealed
                Gv[j, tau] = prob.add_variable(f"g_{j}_{tau}", 0, Q, cat="Integer")    # requested fraction g/Q
                prob += Gv[j, tau] >= Q * S[j, tau]
    prob += pulp.lpSum(Gv.values())
    npairs = 0
    for a in cells:
        for b in cells:
            if a <= b and (a | b) == full:
                ks = set(keys(a)) | set(keys(b))
                ks = [k for k in ks if k in S]
                if not ks: return dict(win=False, why=f"covering pair {a:b},{b:b} cannot be killed")
                prob += pulp.lpSum(S[k] for k in ks) >= 1; npairs += 1
    ncut = 0
    for it in range(max_iter):
        st = prob.solve(game.solver(300))
        if st.status.name == "Infeasible":
            return dict(win=False, why="no affordable seal plan", iters=it, pairs=npairs)
        if not st.has_solution: return dict(win=None, why=st.status.name, iters=it)
        plan = {j: {} for j in range(3, n)}
        for (j, tau), v in Gv.items():
            g = round(v.value())
            if g > 0: plan[j][tau] = g / Q
        worst = []; ok = True
        for j in range(3, n):
            val, m = adversary_lp(j, plan, anc, t)
            worst.append(val)
            if val is not None and val > t + 1e-7:
                ok = False
                # support of earlier responses in m*
                # m* stops being a legal play if some earlier request takes a larger fraction of a
                # parent cell than response i leaves:  g_i(par)/Q > 1 - p*/mass*
                terms = []
                for i in range(3, j):
                    low = (1 << i) - 1; pin = {}; pall = {}
                    for tau, mv in m.items():
                        par = tau & low
                        if not par: continue
                        pall[par] = pall.get(par, 0.0) + mv
                        if (tau >> i) & 1: pin[par] = pin.get(par, 0.0) + mv
                    for par, pv in pin.items():
                        if pv > 1e-9 and (i, par) in Gv:
                            thr = 1 - pv / pall[par]
                            need = math.floor(Q * thr + 1e-7) + 1
                            if need <= Q:
                                bb = prob.add_variable(f"c_{ncut}_{i}_{par}", cat="Binary")
                                prob += Gv[i, par] >= need * bb; terms.append(bb)
                b0 = prob.add_variable(f"b_{ncut}", cat="Binary"); ncut += 1
                prob += pulp.lpSum(Gv[j, tau] * (mv / Q) for tau, mv in m.items() if (j, tau) in Gv) <= t + 8.0 * (1 - b0)
                prob += pulp.lpSum(terms) + b0 >= 1
        if verbose: print(f"  iter {it}: requested cells per round {[len(plan[j]) for j in range(3, n)]}, adversary max seal mass {[None if w is None else round(w, 4) for w in worst]}", flush=True)
        if ok:
            return dict(win=True, plan=plan, seal_mass=worst, iters=it, pairs=npairs)
    return dict(win=None, why="iteration cap", iters=max_iter)


def show_plan(plan, n):
    names = "EFG" + "".join(str(i) for i in range(3, n))
    for j, taus in plan.items():
        print(f"   request before response {j}:", ", ".join("".join(names[i] for i in range(j) if (tau >> i) & 1) + (":all" if f >= 1 else ":%g" % f) for tau, f in sorted(taus.items())))


if __name__ == "__main__":
    x, y, z, t = (float(Fraction(a)) for a in sys.argv[1:5])
    if "--notrace" in sys.argv:
        NOTRACE = True; sys.argv.remove("--notrace"); print("DIAGNOSTIC: responses are forbidden to meet G (not a sound rule)")
    ns = [int(sys.argv[5])] if len(sys.argv) > 5 and sys.argv[5].isdigit() else [5, 6, 7]
    for n in ns:
        r = solve(x, y, z, t, n, verbose="-v" in sys.argv)
        print(f"anchor ({x:g},{y:g},{z:g}) t={t:g} named edges n={n}: ",
              "WIN" if r["win"] else ("STUCK" if r["win"] is False else "UNDECIDED"), {k: v for k, v in r.items() if k not in ("plan", "win")}, flush=True)
        if r["win"]:
            show_plan(r["plan"], n); break
