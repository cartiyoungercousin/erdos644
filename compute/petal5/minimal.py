"""PETAL §27.4: minimal tau > T subfamilies of pooled A at small k, and their (7,2) status.
Usage: py minimal.py k T tauA tauF d m samples seed

1. Cut generation: H' = {} ; repeat { S = min hitting set of H' (exact ILP); if |S| > T stop; add a random member of the
   pooled family avoiding S (class chosen at random among feasible; leak placed in pool with prob. 1/2, else anywhere) }.
2. Deletion-minimalisation in random order: drop E if tau(H' - E) > T still (exact ILP each time).  Result: an
   inclusion-minimal subfamily with tau > T (tau-critical).
3. SAT (CaDiCaL): <= 7 members of H' with no 2-point cover (clause per pair x <= y of points: some chosen member misses
   both); confirmed by the brute-force pair test.
Note: '(7,2) fails for every minimal tau > T subfamily' is equivalent to 'no subfamily with tau > T has (7,2)', since
(7,2)-failure is inherited by superfamilies and every tau > T subfamily contains a minimal one.
"""
import sys, os, random, itertools, time
GEN = os.environ.get("GEN", "lp")
BATCH = int(os.environ.get("BATCH", "10"))
PROG = os.environ.get("PROG") == "1"
import numpy as np, highspy
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
sys.path.insert(0, os.path.dirname(__file__))
from pool_strip import Fam, two_cover, tau_profile


def min_hs(N, edges):
    h = highspy.Highs(); h.setOptionValue("output_flag", False)
    for _ in range(N): h.addVar(0, 1)
    h.changeColsCost(N, np.arange(N, dtype=np.int32), np.ones(N))
    h.changeColsIntegrality(N, np.arange(N, dtype=np.int32), np.ones(N, dtype=np.uint8))
    for E in edges:
        idx = np.array(sorted(E), dtype=np.int32)
        h.addRow(1, highspy.kHighsInf, len(idx), idx, np.ones(len(idx)))
    h.run()
    x = h.getSolution().col_value
    return {i for i in range(N) if x[i] > 0.5}


def rand_member(F, S, rnd):
    cs = [c for c in (0, 1) if F.feasible(S, c)]
    if not cs: return None
    c = rnd.choice(cs)
    k = F.k
    own_free = sorted(F.R[c] - S)
    j = rnd.randint(k - F.d[c], min(k, len(own_free)))
    own = set(rnd.sample(own_free, j))
    rest_pool = sorted((F.allowed_rest(c) - S) - own)
    if rnd.random() < 0.5:
        pref = [x for x in rest_pool if F.reg[x] == 2]
        other = [x for x in rest_pool if F.reg[x] != 2]
        rnd.shuffle(pref); rnd.shuffle(other)
        rest = pref + other
    else:
        rest = rest_pool[:]; rnd.shuffle(rest)
    E = own | set(rest[:k - j])
    if len(E) < k:  # fill from own arena
        E |= set([x for x in own_free if x not in E][:k - len(E)])
    assert len(E) == k and not (E & S) and F.classes(E)
    return frozenset(E)


def lp_weights(N, edges):
    h = highspy.Highs(); h.setOptionValue("output_flag", False)
    for _ in range(N): h.addVar(0, 1)
    h.changeColsCost(N, np.arange(N, dtype=np.int32), np.ones(N))
    for E in edges:
        idx = np.array(sorted(E), dtype=np.int32)
        h.addRow(1, highspy.kHighsInf, len(idx), idx, np.ones(len(idx)))
    h.run()
    return list(h.getSolution().col_value), h.getInfo().objective_function_value


def cheapest_member(F, w, S, rnd, noise=1e-3):
    """member avoiding S of least weight w (random tie-break), or None."""
    best = None
    for c in (0, 1):
        if not F.feasible(S, c): continue
        key = {x: w[x] + noise * rnd.random() for x in F.ALL}
        own = sorted(F.R[c] - S, key=lambda x: key[x])[:F.k - F.d[c]]
        rest = sorted((F.allowed_rest(c) - S) - set(own), key=lambda x: key[x])[:F.d[c]]
        E = frozenset(own) | frozenset(rest)
        if len(E) < F.k: continue
        val = sum(w[x] for x in E)
        if best is None or val < best[0]: best = (val, E)
    return best


def generate_lp(F, T, rnd):
    H = []
    while True:  # LP cuts
        w, v = lp_weights(F.N, H)
        b = cheapest_member(F, w, set(), rnd)
        if b[0] >= 1 - 1e-9: break
        if b[1] not in H: H.append(b[1])
        else: break
    while True:  # integer cuts
        S = min_hs(F.N, H)
        if len(S) > T: return H
        w, v = lp_weights(F.N, H)
        for _ in range(BATCH):
            b = cheapest_member(F, w, S, rnd, noise=0.5)
            if b[1] not in H: H.append(b[1])
        if PROG: print("   cuts", len(H), "ilp", len(S), flush=True)


def sat7(N, H):
    vp = IDPool(); y = [vp.id(("y", i)) for i in range(len(H))]
    cl = []
    for p in range(N):
        for q in range(p, N):
            miss = [y[i] for i, E in enumerate(H) if p not in E and q not in E]
            cl.append(miss)
    cl += CardEnc.atmost(y, 7, vpool=vp, encoding=EncType.seqcounter).clauses
    with Solver(name="cadical153", bootstrap_with=cl) as s:
        if not s.solve(): return None
        mod = set(l for l in s.get_model() if l > 0)
    return [H[i] for i in range(len(H)) if y[i] in mod]


if __name__ == "__main__":
    k, T, tA, tF, d, m, samples, seed = map(int, sys.argv[1:9])
    F = Fam(k, tA - 1 + k - d, tF - 1 + k - d, d, d, m)
    print("pooled family k=%d T=%d nA=%d nF=%d d=%d m=%d: t=%.3f delta=%.3f, tau(full)=%d" % (
        k, T, F.n[0], F.n[1], d, m, T / k, d / k, tau_profile(F)), flush=True)
    rnd = random.Random(seed)
    for s in range(samples):
        t0 = time.time()
        if GEN == "lp":
            H = generate_lp(F, T, rnd)
        else:
            H = []
            while True:
                S = min_hs(F.N, H)
                if len(S) > T: break
                H.append(rand_member(F, S, rnd))
        n0 = len(H)
        order = list(range(len(H))); rnd.shuffle(order)
        keep = list(H)
        for i in order:
            E = H[i]
            trial = [x for x in keep if x != E]
            if len(min_hs(F.N, trial)) > T: keep = trial
        tau = len(min_hs(F.N, keep))
        # minimality check: every single deletion drops tau to <= T
        crit = all(len(min_hs(F.N, [x for x in keep if x != E])) <= T for E in keep)
        cls = [F.classes(set(E))[0] for E in keep]
        pool_use = sum(1 for E in keep if E & F.R[2])
        seven = sat7(F.N, keep)
        bf = None if seven is None else two_cover([set(E) for E in seven])
        print("sample %d: cut-generated %d, minimal %d members (A %d, F %d, %d using the pool), tau = %d, critical = %s; "
              "(7,2): %s%s  [%.1fs]" % (s, n0, len(keep), cls.count(0), cls.count(1), pool_use, tau, crit,
                                        "HOLDS (no 7 members without 2-cover)" if seven is None else "fails (%d members, brute-force 2-cover: %s)" % (len(seven), bf),
                                        "", time.time() - t0), flush=True)
