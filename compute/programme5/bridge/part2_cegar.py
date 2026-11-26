"""Bridge-seed adversary CEGAR (part 2). Grows a seven-free family H on V = R1 | R2 | P:
repeat: S = a minimum transversal of H (exact ILP, random tie-break); find a k-set B avoiding S
(CP-SAT) with (i) allowed shape profile, (ii) |B & B'| in spectrum(k) for all B' in H (if --spec),
(iii) B meets W(O) for every recorded cut O (O + B would be a good seven otherwise);
then exact SAT seven-test of H + B with B forced; if a seven exists, record its other members O as a cut.
If no B avoids S, delete 1-2 members (preferring members of recent killing sevens) and continue.
H is seven-free at every step [computed exact]; best tau is exact; the search itself is [heuristic].
Usage: py part2_cegar.py k a b p shape spec start seed seconds tag
 shape: seed (cluster1/cluster2/E-bridge/K-bridge profiles) | bridge (any member with both feet >= 2) | free
 spec: 1/0;  start: efg | empty"""
import sys, time, json, random, collections
from part2_lib import spectrum, record, tau, seven, seven_budget, check_seven, uncovered_points, cotype_summary
from ortools.sat.python import cp_model

k, a, b, p = map(int, sys.argv[1:5]); shape = sys.argv[5]; usespec = sys.argv[6] == "1"; start = sys.argv[7]
seed = int(sys.argv[8]); SECS = float(sys.argv[9]); tag = sys.argv[10]
TL = float(sys.argv[11]) if len(sys.argv) > 11 else 1.0
n = a + b + p; R1 = set(range(a)); R2 = set(range(a, a + b)); P = set(range(a + b, n))
rng = random.Random(seed); SPEC = spectrum(k); T0 = time.time()
LOG = open(f"logs/part2_{tag}.log", "w")
def log(*s):
    msg = " ".join(map(str, s)); print(msg, flush=True); LOG.write(msg + "\n"); LOG.flush()

g = round(k / 7)
def rr(x): return int(round(x))
TYPES = {  # name: (r1 range, r2 range, p range)
    "C1": ((k - g, k), (0, g), (0, g)),
    "C2": ((0, g), (k - g, k), (0, g)),
    "E": ((rr(3 * k / 7) - 1, rr(3 * k / 7) + 1), (rr(5 * k / 14) - 1, rr(5 * k / 14) + 1), (rr(3 * k / 14) - 1, k)),
    "K": ((rr(k / 2) - 1, rr(k / 2) + 1), (rr(k / 2) - 1, rr(k / 2) + 1), (0, 2)),
}
def prof(B): return (len(B & R1), len(B & R2), len(B & P))
def label(B):
    pr = prof(B)
    for t, rg in TYPES.items():
        if all(lo <= x <= hi for x, (lo, hi) in zip(pr, rg)): return t
    return "o%d.%d.%d" % pr

log(f"k={k} n={n} |R1|={a} |R2|={b} |P|={p} shape={shape} spec={usespec} start={start} seed={seed} "
    f"record={record(k)} spectrum={SPEC}")

H = []  # list of (id, frozenset)
nid = 0
def add(B):
    global nid
    H.append((nid, frozenset(B))); nid += 1
if start == "efg":
    F = set(sorted(R1)[:k]) if a >= k else set(sorted(R1)) | set(sorted(P)[:k - a])
    Gs = set(sorted(R2)[:k]) if b >= k else set(sorted(R2)) | set(sorted(P)[-(k - b):])
    e1, e2 = rr(3 * k / 7), rr(5 * k / 14); ep = k - e1 - e2
    Eset = set(sorted(F & R1)[:e1]) | set(sorted(Gs & R2)[:e2]) | set(sorted(P - F - Gs)[:ep])
    if len(Eset) < k: Eset |= set(sorted(V for V in range(n) if V not in Eset and V not in F and V not in Gs)[:k - len(Eset)])
    for X in (Eset, F, Gs): add(X)
    log("start E,F,G profiles:", [prof(X) for X in (Eset, F, Gs)], "|EF|,|EG|,|FG| =",
        len(Eset & F), len(Eset & Gs), len(F & Gs))
    assert len(Eset) == k and seven([X for _, X in H], n) is None

cuts = []  # (frozenset of member ids in O, W, pattern)
pattern_count = collections.Counter()
best = (-1, None); it = 0; stuck = 0; best_logged = [-1]

def find_member(S):
    m = cp_model.CpModel()
    x = [m.NewBoolVar(f"x{v}") for v in range(n)]
    m.Add(sum(x) == k)
    for v in S: m.Add(x[v] == 0)
    r1 = sum(x[v] for v in R1); r2 = sum(x[v] for v in R2); pp = sum(x[v] for v in P)
    if shape == "seed":
        ind = []
        for t, ((l1, h1), (l2, h2), (l3, h3)) in TYPES.items():
            z = m.NewBoolVar(t); ind.append(z)
            for e, l, h in ((r1, l1, h1), (r2, l2, h2), (pp, l3, h3)):
                m.Add(e >= l).OnlyEnforceIf(z); m.Add(e <= h).OnlyEnforceIf(z)
        m.AddBoolOr(ind)
    elif shape == "bridge":
        pass  # any profile, but clusters arise naturally; feet constraint only applies to start
    dom = cp_model.Domain.FromValues(SPEC if usespec else list(range(k)))
    for _, Bp in H:
        m.AddLinearExpressionInDomain(sum(x[v] for v in Bp), dom)
    for O, W, _ in cuts:
        m.AddBoolOr([x[v] for v in W])
    for Bt in tabu:
        m.AddBoolOr([x[v].Not() for v in Bt])
    deg = [sum(1 for _, Bp in H if v in Bp) for v in range(n)]
    m.Minimize(sum((4 * deg[v] + rng.randint(0, 3 + len(H) // 4)) * x[v] for v in range(n)))
    s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = TL; s.parameters.num_workers = 1
    s.parameters.randomize_search = True
    s.parameters.random_seed = rng.randint(0, 10**6)
    st = s.Solve(m)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        return frozenset(v for v in range(n) if s.Value(x[v]))
    return None if st == cp_model.INFEASIBLE else "timeout"

recent = collections.Counter(); tabu = []; nunk = [0]; BUDGET = 20000
while time.time() - T0 < SECS:
    it += 1
    fam = [B for _, B in H]
    t, S = tau(fam, n, rng) if fam else (0, [])
    if t > best[0] or (t == best[0] and len(H) > len(best[1])):
        best = (t, list(fam))
        json.dump({"k": k, "n": n, "sizes": [a, b, p], "shape": shape, "spec": usespec, "tau": t,
                   "family": [sorted(B) for B in fam]}, open(f"logs/part2_best_{tag}.json", "w"))
        if t > best_logged[0]:
            best_logged[0] = t
            log(f"[{time.time()-T0:.0f}s] it={it} NEW BEST tau={t} |H|={len(H)} types="
                f"{dict(collections.Counter(label(B) for B in fam))}")
        if t > record(k):
            log("*** CANDIDATE RECORD: tau", t, "> record", record(k), "(H seven-free by construction) ***")
    # find a member avoiding S
    tries = 0; newB = None
    while tries < 150:
        tries += 1
        B = find_member(S)
        if B is None or B == "timeout": break
        fam2 = fam + [B]
        ch = seven_budget(fam2, n, [len(fam)], BUDGET)
        if ch is None: newB = B; break
        if ch == "unknown":
            nunk[0] += 1; tabu.append(B); continue
        O = [i for i in ch if i != len(fam)]
        Oids = frozenset(H[i][0] for i in O)
        W = uncovered_points([fam[i] for i in O], n)
        pat = " ".join(sorted(label(fam[i]) for i in O)) + " + " + label(B)
        pattern_count[pat] += 1
        if len(pattern_count) <= 3 and pattern_count[pat] == 1 or sum(pattern_count.values()) % 100 == 0:
            mem = [fam[i] for i in O] + [B]
            log(f"  killing seven #{sum(pattern_count.values())} (tau={t}, |H|={len(H)}): pattern {pat}")
            log("     profiles(R1,R2,P):", [prof(X) for X in mem], " seed members in it:",
                [("EFG"[H[i][0]]) for i in O if H[i][0] < 3] if start == "efg" else [])
            log("     pairwise:", [[len(X & Y) for Y in mem] for X in mem])
            log("     co-types:", cotype_summary(mem, [("R1", R1), ("R2", R2), ("P", P)], n))
        cuts.append((Oids, frozenset(W), pat))
        for i in Oids: recent[i] += 1
    if newB is not None:
        add(newB); stuck = 0
        if it % 50 == 0:
            log(f"[{time.time()-T0:.0f}s] it={it} tau={t} |H|={len(H)} cuts={len(cuts)} unknown={nunk[0]}")
        continue
    # stuck: delete
    stuck += 1
    ids = [i for i, _ in H]
    if not ids: break
    weights = [1 + 3 * recent.get(i, 0) for i in ids]
    ndel = 1 if rng.random() < 0.6 else 2
    dele = set()
    for _ in range(ndel): dele.add(rng.choices(ids, weights)[0])
    H = [(i, B) for i, B in H if i not in dele]
    cuts = [c for c in cuts if not (c[0] & dele)]
    recent = collections.Counter({i: c // 2 for i, c in recent.items() if i not in dele})
    if stuck % 25 == 0:
        log(f"[{time.time()-T0:.0f}s] it={it} tau={t} |H|={len(H)} cuts={len(cuts)} stuck={stuck} unknown={nunk[0]}")

log(f"[{time.time()-T0:.0f}s] it={it} final |H|={len(H)} cuts={len(cuts)} budget-unknown rejections={nunk[0]}")
log(f"DONE best tau={best[0]} |H|={len(best[1])} record={record(k)} gap={record(k)-best[0]}")
fam = best[1]
t2, _ = tau(fam, n); assert t2 == best[0]
r = seven_budget(fam, n, [], 2000000)
assert r is None or r == "unknown"
log("re-check best family from scratch: tau", t2, "; full seven SAT:", "UNSAT (seven-free, exact)" if r is None else
    "budget exhausted (seven-freeness rests on the per-addition UNSAT proofs)")
log("best types:", dict(collections.Counter(label(B) for B in fam)))
log("top killing-seven patterns (other members + new member):")
for pat, c in pattern_count.most_common(12): log(f"  {c:5d}  {pat}")
