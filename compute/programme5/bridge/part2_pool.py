"""Bridge-seed POOL families (part 2).
1. Pool: V = R1 | R2 | P; start with the seed triple E, F, G (F in R1, G in R2, |EF|=3k/7, |EG|=5k/14,
   |FG|=0, E has 3k/14 private points); then random members of shape types C1 (cluster in R1), C2, E-bridge,
   K-bridge, accepted only if every pairwise intersection with accepted members is in spectrum(k) (if spec=1).
2. tau(pool) exact (HiGHS ILP); first good seven of the pool (exact SAT) is logged structurally = the
   'killing seven' of the seed pool.
3. Deletion: incremental CaDiCaL; repeatedly find a good seven and delete one non-seed member of it
   (strategy: rand | maxdeg = the member of the seven lying in most other found sevens | pref<T> = prefer type T),
   until UNSAT => seven-free [computed exact]; then greedy re-insertion of deleted members (forced-member SAT).
   tau of the final seven-free family exact. The search is [heuristic].
Usage: py part2_pool.py k a b p spec poolsize strategy seed seconds tag [w]"""
import sys, time, json, random, collections, itertools
import numpy as np
from part2_lib import spectrum, record, tau, seven, check_seven, uncovered_points, cotype_summary
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

k, a, b, p = map(int, sys.argv[1:5]); usespec = sys.argv[5] == "1"; POOL = int(sys.argv[6])
strat = sys.argv[7]; seed = int(sys.argv[8]); SECS = float(sys.argv[9]); tag = sys.argv[10]
w = int(sys.argv[11]) if len(sys.argv) > 11 else 1
n = a + b + p; R1 = list(range(a)); R2 = list(range(a, a + b)); P = list(range(a + b, n))
sR1, sR2, sP = set(R1), set(R2), set(P)
rng = random.Random(seed); SPEC = set(spectrum(k)); T0 = time.time()
LOG = open(f"logs/part2_{tag}.log", "w")


def log(*s):
    msg = " ".join(map(str, s)); print(msg, flush=True); LOG.write(msg + "\n"); LOG.flush()


g = round(k / 7)
rr = lambda x: int(round(x))
TYPES = {"C1": ((k - g, k), (0, g), (0, g)), "C2": ((0, g), (k - g, k), (0, g)),
         "E": ((rr(3 * k / 7) - w, rr(3 * k / 7) + w), (rr(5 * k / 14) - w, rr(5 * k / 14) + w), (rr(3 * k / 14) - w, k)),
         "K": ((rr(k / 2) - w, rr(k / 2) + w), (rr(k / 2) - w, rr(k / 2) + w), (0, 2 * w))}


def prof(B): return (len(B & sR1), len(B & sR2), len(B & sP))


def label(B):
    pr = prof(B)
    for t, rg in TYPES.items():
        if all(lo <= x <= hi for x, (lo, hi) in zip(pr, rg)): return t
    return "o%d.%d.%d" % pr


def mask(B): return sum(1 << v for v in B)


log(f"k={k} n={n} sizes={a},{b},{p} spec={usespec} spectrum={sorted(SPEC)} pool={POOL} strat={strat} seed={seed} "
    f"w={w} record={record(k)}")

# seed triple
F = set(R1[:k]) if a >= k else set(R1) | set(P[:k - a])
G = set(R2[:k]) if b >= k else set(R2) | set(P[len(P) - (k - b):])
e1, e2 = rr(3 * k / 7), rr(5 * k / 14)
E = set(sorted(F & sR1)[:e1]) | set(sorted(G & sR2)[:e2])
rest = [v for v in P if v not in F and v not in G] + [v for v in range(n) if v not in F and v not in G and v not in sP]
E |= set(rest[:k - len(E)])
assert len(E) == k, "no room for E's private points"
fam = [frozenset(E), frozenset(F), frozenset(G)]
log("seed E,F,G profiles", [prof(X) for X in fam], "|EF|,|EG|,|FG|", len(E & F), len(E & G), len(F & G))
masks = np.array([mask(X) for X in fam], dtype=np.uint64)


def compatible(B):
    c = np.uint64(mask(B))
    s = np.bitwise_count(np.bitwise_and(masks, c))
    if (s == k).any(): return False
    if not usespec: return True
    return all(int(v) in SPEC for v in np.unique(s))


tried = 0; seen = set(map(mask, fam)); tl = list(TYPES)
while len(fam) < POOL and tried < 40 * POOL:
    tried += 1
    t = rng.choice(tl); (l1, h1), (l2, h2), (l3, h3) = TYPES[t]
    r1 = rng.randint(l1, min(h1, a))
    if min(h2, b, k - r1) < l2: continue
    r2 = rng.randint(l2, min(h2, b, k - r1)); q = k - r1 - r2
    if not (l3 <= q <= h3) or q > p or q < 0: continue
    B = frozenset(rng.sample(R1, r1) + rng.sample(R2, r2) + rng.sample(P, q))
    if mask(B) in seen: continue
    if compatible(B):
        fam.append(B); seen.add(mask(B)); masks = np.append(masks, np.uint64(mask(B)))
m = len(fam)
log(f"[{time.time()-T0:.0f}s] pool |H|={m} (tried {tried}) types={dict(collections.Counter(label(B) for B in fam))}")
t0, _ = tau(fam, n); log(f"tau(pool) = {t0}  [computed exact]")


def describe(ch, famx, title):
    mem = [famx[i] for i in ch]
    log(title)
    for j, i in enumerate(ch):
        log(f"   M{j}: {label(famx[i]):>8} profile(R1,R2,P)={prof(famx[i])}" + (f"  [seed {'EFG'[i]}]" if i < 3 else ""))
    inter = [[len(x & y) for y in mem] for x in mem]
    log("   pairwise |Mi & Mj|:", inter)
    cs = cotype_summary(mem, [("R1", sR1), ("R2", sR2), ("P", sP)], n)
    log("   co-types (indices of members MISSING the point) per cell:", cs)


def build_solver(alive):
    cnf = CardEnc.atmost(lits=list(range(1, m + 1)), bound=7, top_id=m, encoding=EncType.seqcounter)
    S = Cadical153(bootstrap_with=cnf.clauses)
    for x in range(n):
        for y in range(x, n):
            S.add_clause([i + 1 for i, B in enumerate(fam) if x not in B and y not in B])
    for i in range(m):
        if not alive[i]: S.add_clause([-(i + 1)])
    return S


alive = [True] * m; S = build_solver(alive)
pat = collections.Counter(); inseven = collections.Counter(); nsev = 0; first = True; done = False
while time.time() - T0 < SECS:
    if not S.solve(): done = True; break
    ch = [v - 1 for v in S.get_model() if 0 < v <= m]
    assert check_seven([fam[i] for i in ch], n) and all(alive[i] for i in ch)
    nsev += 1
    if first:
        describe(ch, fam, "KILLING SEVEN of the seed pool (first found, verified by brute force):"); first = False
    pat[" ".join(sorted(label(fam[i]) + ("*" if i < 3 else "") for i in ch))] += 1
    for i in ch: inseven[i] += 1
    cand = [i for i in ch if i >= 3]
    if strat == "rand": d = rng.choice(cand)
    elif strat == "maxdeg": d = max(cand, key=lambda i: (inseven[i], rng.random()))
    else:
        pref = [i for i in cand if label(fam[i]) == strat[4:]]
        d = rng.choice(pref or cand)
    alive[d] = False; S.add_clause([-(d + 1)])
    if nsev % 200 == 0:
        log(f"[{time.time()-T0:.0f}s] sevens={nsev} alive={sum(alive)}")
cur = [i for i in range(m) if alive[i]]
log(f"[{time.time()-T0:.0f}s] deletion {'finished: UNSAT (seven-free)' if done else 'TIMEOUT'} after {nsev} sevens; "
    f"|H|={len(cur)}")
log("seven type patterns (top; * = seed member):")
for q, c in pat.most_common(8): log(f"  {c:5d}  {q}")
if done:
    tmid, _ = tau([fam[i] for i in cur], n); log(f"tau after deletion = {tmid}")
    dead = [i for i in range(m) if not alive[i]]; rng.shuffle(dead); added = 0
    for d in dead:
        if time.time() - T0 > SECS * 1.3: break
        if S.solve(assumptions=[d + 1]): continue  # d would complete a good seven
        alive[d] = True; added += 1
        S.delete(); S = build_solver(alive)
    final = [fam[i] for i in range(m) if alive[i]]
    log(f"re-inserted {added}; final |H|={len(final)}")
    assert seven(final, n) is None
    tf, Sf = tau(final, n)
    log(f"FINAL seven-free (exact SAT, re-checked from scratch) |H|={len(final)} tau={tf} record={record(k)} "
        f"gap={record(k)-tf} types={dict(collections.Counter(label(B) for B in final))}")
    if usespec:
        ok = all(len(x & y) in SPEC for x, y in itertools.combinations(final, 2))
        log("spectrum respected (all pairs re-checked):", ok)
    json.dump({"k": k, "n": n, "sizes": [a, b, p], "spec": usespec, "tau": tf, "seven_free": True,
               "family": [sorted(B) for B in final]}, open(f"logs/part2_fam_{tag}.json", "w"))
    if tf > record(k): log("*** CANDIDATE RECORD ***")
