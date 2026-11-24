# CORE Part III, M1: pile branch with the kernel Y fixed.  py m1_search.py
# Reduced ground set V' = V - Y, mass 1 + t (k = 1).  Co-edges containing Y are identified with
# their traces on V' (mass <= t).  Classes = points of a Fano plane on V'; sets = unions of classes.
import itertools, pulp
from fractions import Fraction as Fr
LINES = [frozenset(L) for L in [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]]
PTS = range(7)
def pencil(v): return [L for L in LINES if v in L]

def justified(S, piled):
    """S avoids the pairwise intersections of three piled sets with empty common intersection (in V')"""
    for A, B, C in itertools.combinations(piled, 3):
        if A & B & C: continue
        if not (S & ((A & B) | (A & C) | (B & C))): return (A, B, C)
    return None

# ---- (a) strict version: every request is a line of the plane -------------------------------
print("(a) strict: requests = lines of the plane")
res = set()
for l1, l2 in itertools.permutations(LINES, 2):
    v12 = next(iter(l1 & l2))
    for l3 in LINES:
        if v12 in l3 or l3 in (l1, l2): continue
        piled = [l1, l2, l3]              # K_1, K_2 contain Y; S_3 triangle-type, answered high
        grew = True
        while grew:
            grew = False
            for L in LINES:
                if L not in piled and justified(L, piled):
                    piled.append(L); grew = True
        # is Y complete?  Y lies in the piled co-edges; needs three concurrent ones
        complete = any(all(L in piled for L in pencil(v)) for v in PTS)
        res.add((len(piled), complete))
print("   (number of piled lines at closure, Y inside a pencil) over all 168 starts:", res)

# LP: Y must be requested in one more line (completing a pencil); how large can omega be?
def lp_strict(t, omega):
    l1, l2, l3 = LINES[0], LINES[1], LINES[3]          # triangle 012 / 034 / 135 ; vertices 0,1,3
    pr = pulp.LpProblem("s", pulp.LpMinimize)
    w = [pr.add_variable("w%d" % v, 0, 2) for v in PTS]
    pr += 0 * w[0]
    pr += pulp.lpSum(w) == 1 + t
    pr += pulp.lpSum(w[v] for v in l1) == t
    pr += pulp.lpSum(w[v] for v in l2) == t
    for L in LINES: pr += pulp.lpSum(w[v] for v in L) <= t
    pr += pulp.lpSum(w[v] for v in LINES[2]) <= t - omega   # third line through v12 = 0 carries Y
    st = pr.solve(pulp.HiGHS(msg=False))
    return ('feasible' if st.has_solution else 'INFEASIBLE')
for t in (0.76, 0.751):
    eps = t - 0.75
    print("   t = %.3f: Y requested in the third pencil line: omega = %.4f -> %s, omega = %.4f -> %s"
          % (t, 4*eps - 1e-4, lp_strict(t, 4*eps - 1e-4), 4*eps + 1e-3, lp_strict(t, 4*eps + 1e-3)))

# ---- (b) weak version: helpers = any union of <= 4 classes ---------------------------------
print("(b) weak: helper requests = arbitrary unions of classes")
l1, l2 = LINES[0], LINES[1]; v12 = 0; cev = LINES[2]      # cev = third line through v12
allsets = [frozenset(s) for r in (3,) for s in itertools.combinations(PTS, r)]   # helpers are t-sets: three classes
best = None
for l3 in [L for L in LINES if v12 not in L]:
    piled = [l1, l2, l3]; order = []
    # breadth-first: add justified sets until the cevian through v12 is justified
    for depth in range(4):
        if justified(cev, piled): break
        new = [S for S in allsets if S not in piled and justified(S, piled)]
        # prefer a helper that makes the cevian justified at once
        hit = [S for S in new if justified(cev, piled + [S])]
        pick = (hit or new)[0]; piled.append(pick); order.append(pick)
    if justified(cev, piled) and (best is None or len(order) < len(best[1])): best = (l3, order, justified(cev, piled))
l3, helpers, trip = best
print("   lines K1 =", sorted(l1), " K2 =", sorted(l2), " S3 =", sorted(l3))
print("   helpers (piled, in order):", [sorted(h) for h in helpers])
print("   cevian", sorted(cev), "justified by the triple", [sorted(x) for x in trip])

def lp_weak(t, sense, sets_le):
    pr = pulp.LpProblem("w", sense)
    w = [pr.add_variable("w%d" % v, 0, 2) for v in PTS]
    pr += w[v12]
    pr += pulp.lpSum(w) == 1 + t
    pr += pulp.lpSum(w[v] for v in l1) == t
    pr += pulp.lpSum(w[v] for v in l2) == t
    for L in sets_le: pr += pulp.lpSum(w[v] for v in L) <= t
    for L in [l3] + helpers: pr += pulp.lpSum(w[v] for v in L) == t      # piled replies are full requests
    st = pr.solve(pulp.HiGHS(msg=False))
    return ('feasible' if st.has_solution else 'INFEASIBLE'), [x.value() for x in w]
for t in (Fr(19, 25), Fr(751, 1000)):
    sets_le = LINES + helpers
    lo = lp_weak(float(t), pulp.LpMinimize, sets_le); hi = lp_weak(float(t), pulp.LpMaximize, sets_le)
    print("   t = %s: LP %s; class v12 (= |K1∩K2| - omega) may range over [%.5f, %.5f]" % (t, lo[0], lo[1][v12], hi[1][v12]))
    # exact rational verification of one solution
    w = [Fr(x).limit_denominator(10**6) for x in hi[1]]
    ok = (sum(w) == 1 + t and sum(w[v] for v in l1) == t and sum(w[v] for v in l2) == t
          and all(sum(w[v] for v in L) <= t for L in sets_le) and min(w) >= 0
          and all(sum(w[v] for v in L) == t for L in [l3] + helpers))
    print("      rational solution", [str(x) for x in w], "verified exactly:", ok)

# ---- (c) is the pile forced at the cevian?  real sets, t = 19/25, N = 1.9 -------------------
print("(c) the decisive request (cevian through v12) at t = 19/25, N = 1.9 (k = 100, T = 76, omega = 14)")
t = Fr(19, 25); k = 100; T = 76; om = 14
st, sol = lp_weak(float(t), pulp.LpMaximize, LINES + helpers)
w = [int(Fr(x).limit_denominator(10**6) * k) for x in sol]
cls = {}; pos = 0
for v in PTS: cls[v] = set(range(pos, pos + w[v])); pos += w[v]
Y = set(range(pos, pos + om)); V = list(range(pos + om)); N = len(V); c = N - k
def U(S): return set().union(*[cls[v] for v in S])
def tri_excess(K1, K2, K3):
    """Theorem T for three co-edges: min over the split of kappa of (max load) - T"""
    a = (K1 & K2) - K3; b = (K1 & K3) - K2; d = (K2 & K3) - K1
    e1 = K1 - K2 - K3; e2 = K2 - K1 - K3; e3 = K3 - K1 - K2
    g = set(V) - K1 - K2 - K3; ka = len(K1 & K2 & K3)
    base = [len(a) + len(e3) + len(g), len(b) + len(e2) + len(g), len(d) + len(e1) + len(g)]
    best = min(max(base[0] + x, base[1] + y, base[2] + ka - x - y)
               for x in range(ka + 1) for y in range(ka + 1 - x))
    return max(best, len(e1) + len(e2) + len(e3)) - T
A, B, C = trip
names = {A: "A", B: "B", C: "C"}
print("   class sizes", w, " justification triple A,B,C =", [sorted(x) for x in trip])
S = U(cev)
for label, D in [("pile: D = Y", set(Y))] + [("D inside class %d = %s∩%s" % (next(iter(P & Q)), names[P], names[Q]),
                                               set(sorted(U(P & Q))[:om])) for P, Q in ((A,B),(A,C),(B,C)) if P & Q] \
                 + [("D inside class %d (in one of A,B,C only)" % v, set(sorted(cls[v])[:om]))
                    for v in PTS if v not in cev and sum(v in X for X in trip) == 1][:2]:
    K = S | D
    ex = {names[P] + names[Q]: tri_excess(U(P) | Y, U(Q) | Y, K) for P, Q in ((A,B),(A,C),(B,C))}
    print("   %-38s Theorem-T excess over T for the pairs: %s" % (label, ex))
# pile at the cevian => the seven co-edges cover all pairs of V
import random
def pair_covered(Ks):
    for x in V:
        Ix = [K for K in Ks if x in K]
        if not Ix: return False
        for y in V:
            if y > x and not any(y in K for K in Ix): return False
    return True
m_line = [L for L in LINES if not (L & {next(iter(l1 & l2)), next(iter(l1 & l3)), next(iter(l2 & l3))})][0]
seven = [U(l1) | Y, U(l2) | Y, U(l3) | Y, U(m_line) | Y, U(cev) | Y]
for L in LINES:
    if L not in (l1, l2, l3, m_line, cev):
        rest = [v for v in V if v not in U(L) and v not in Y]; random.shuffle(rest)
        seven.append(U(L) | set(rest[:c - len(U(L))]))            # nasty dump, off Y
print("   if he piles at the cevian: sizes", [len(K) for K in seven], "c =", c, " pair cover:", pair_covered(seven))
