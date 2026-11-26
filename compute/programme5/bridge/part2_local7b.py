"""Local killing sevens of the bridge seed (part 2). Exact CP-SAT feasibility [computed exact]:
does a good seven exist consisting of a given subset of the seed triple {E, F, G} plus r free members of
prescribed shape types, with ALL pairwise intersections (free-free and free-seed) in spectrum(k) (if spec)?
V = R1 | R2 | P with the seed triple placed as in part2_cegar.py / part2_pool.py.
Feasible => the seven is printed with profiles, pairwise intersections and co-type pattern, and re-verified
by brute force. Infeasible => no good seven of that pattern exists (exact, CP-SAT OPTIMAL/INFEASIBLE status).
Usage: py part2_local7.py k a b p  (runs the built-in pattern list)"""
import sys, time, collections
from ortools.sat.python import cp_model
from part2_lib import spectrum, record, check_seven, cotype_summary

k, a, b, p = map(int, sys.argv[1:5]); tag = sys.argv[5] if len(sys.argv) > 5 else f"local7_k{k}_{a}_{b}_{p}"
n = a + b + p; R1 = list(range(a)); R2 = list(range(a, a + b)); P = list(range(a + b, n))
sR1, sR2, sP = set(R1), set(R2), set(P)
LOG = open(f"logs/part2_{tag}.log", "w")


def log(*s):
    msg = " ".join(map(str, s)); print(msg, flush=True); LOG.write(msg + "\n"); LOG.flush()


g = round(k / 7); rr = lambda x: int(round(x)); w = 1
TYPES = {"C1": ((k - g, k), (0, g), (0, g)), "C2": ((0, g), (k - g, k), (0, g)),
         "E": ((rr(3 * k / 7) - w, rr(3 * k / 7) + w), (rr(5 * k / 14) - w, rr(5 * k / 14) + w), (rr(3 * k / 14) - w, k)),
         "K": ((rr(k / 2) - w, rr(k / 2) + w), (rr(k / 2) - w, rr(k / 2) + w), (0, 2 * w)),
         "K0": ((rr(k / 2), rr(k / 2)), (rr(k / 2), rr(k / 2)), (0, 0)),
         "any": ((0, k), (0, k), (0, k))}
F = set(R1[:k]) if a >= k else set(R1) | set(P[:k - a])
G = set(R2[:k]) if b >= k else set(R2) | set(P[len(P) - (k - b):])
e1, e2 = rr(3 * k / 7), rr(5 * k / 14)
E = set(sorted(F & sR1)[:e1]) | set(sorted(G & sR2)[:e2])
rest = [v for v in P if v not in F and v not in G] + [v for v in range(n) if v not in F and v not in G and v not in sP]
E |= set(rest[:k - len(E)]); assert len(E) == k
SEED = {"E": frozenset(E), "F": frozenset(F), "G": frozenset(G)}


def prof(B): return (len(B & sR1), len(B & sR2), len(B & sP))


def solve(seedset, types, spec, extra=None, tl=300):
    m = cp_model.CpModel()
    fixed = [SEED[s] for s in seedset]
    r = len(types)
    X = [[m.NewBoolVar(f"b{i}_{v}") for v in range(n)] for i in range(r)]
    SP = spectrum(k) if spec else list(range(k))
    dom = cp_model.Domain.FromValues(SP)
    for i, t in enumerate(types):
        m.Add(sum(X[i]) == k)
        (l1, h1), (l2, h2), (l3, h3) = TYPES[t]
        for cell, lo, hi in ((R1, l1, h1), (R2, l2, h2), (P, l3, h3)):
            m.Add(sum(X[i][v] for v in cell) >= lo); m.Add(sum(X[i][v] for v in cell) <= hi)
        for B in fixed:
            m.AddLinearExpressionInDomain(sum(X[i][v] for v in B), dom)
        if extra: extra(m, X, i, t)
    for i in range(r):
        for j in range(i + 1, r):
            c = []
            for v in range(n):
                z = m.NewBoolVar(""); m.AddBoolAnd([X[i][v], X[j][v]]).OnlyEnforceIf(z)
                m.AddBoolOr([X[i][v].Not(), X[j][v].Not()]).OnlyEnforceIf(z.Not()); c.append(z)
            m.AddLinearExpressionInDomain(sum(c), dom)
        if i + 1 < r and types[i] == types[i + 1]:  # symmetry breaking: lexicographic-ish on first point weight
            m.Add(sum((1 << min(v, 40)) * 0 + v * X[i][v] for v in range(n)) <= sum(v * X[i + 1][v] for v in range(n)))
    for x in range(n):
        for y in range(x, n):
            if any(x not in B and y not in B for B in fixed): continue
            lits = []
            for i in range(r):
                if x == y: lits.append(X[i][x].Not())
                else:
                    z = m.NewBoolVar(""); m.AddImplication(z, X[i][x].Not()); m.AddImplication(z, X[i][y].Not())
                    lits.append(z)
            m.AddBoolOr(lits)
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = tl; s.parameters.num_workers = 1
    st = s.Solve(m)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        mem = fixed + [frozenset(v for v in range(n) if s.Value(X[i][v])) for i in range(r)]
        return "FEASIBLE", mem
    return ("INFEASIBLE" if st == cp_model.INFEASIBLE else "UNKNOWN (time limit)"), None


PATTERNS = [
    (("E", "F", "G"), ("K", "C1", "C2", "C1")),
    (("E", "F", "G"), ("K", "C1", "C2", "C2")),
    (("E", "F", "G"), ("C1", "C1", "C2", "C2")),
    (("E", "F", "G"), ("E", "E", "E", "E")),
    (("E", "F", "G"), ("K", "E", "E", "E")),
    (("E", "F", "G"), ("K", "K", "E", "E")),
    (("F", "G"), ("K", "K", "C1", "C2", "C1")),
    (("F", "G"), ("K", "K", "K", "C1", "C2")),
]
PATTERNS_OLD = [
    (("E", "F", "G"), ("K", "K", "K", "K")),
    (("E", "F", "G"), ("K0", "K0", "K0", "K0")),
    (("E", "F", "G"), ("K", "K", "K", "E")),
    (("E", "F", "G"), ("K", "K", "C1", "C2")),
    (("F", "G"), ("K", "K", "K", "K", "K")),
    (("E", "F"), ("K", "K", "K", "K", "K")),
    (("E", "F", "G"), ("any", "any", "any", "any")),
    (("E",), ("K", "K", "K", "K", "K", "K")),
    ((), ("K", "K", "K", "K", "K", "K", "K")),
]
log(f"k={k} n={n} sizes={a},{b},{p} spectrum={spectrum(k)} record={record(k)}")
log("seed profiles (R1,R2,P): E", prof(SEED['E']), "F", prof(SEED['F']), "G", prof(SEED['G']))
for seedset, types in PATTERNS:
    for spec in (True, False):
        t0 = time.time()
        st, mem = solve(seedset, types, spec)
        lab = "+".join(seedset) + ("+" if seedset else "") + "+".join(types)
        log(f"[{time.time()-t0:.1f}s] pattern {lab:<32} spec={int(spec)}: {st}")
        if mem:
            assert check_seven(mem, n)
            SP = set(spectrum(k)) if spec else set(range(k))
            assert all(len(x & y) in SP for i, x in enumerate(mem) for y in mem[i + 1:])
            log("     profiles(R1,R2,P):", [prof(B) for B in mem])
            log("     pairwise:", [[len(x & y) for y in mem] for x in mem])
            log("     co-types:", cotype_summary(mem, [("R1", sR1), ("R2", sR2), ("P", sP)], n))
            log("     members:", [sorted(B) for B in mem])
