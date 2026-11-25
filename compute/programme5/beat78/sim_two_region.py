"""Finite-k simulation of the two-region adversary (Theorem O) against mixed request strategies.
Adversary: disjoint R1, R2 of size s = ceil((2-c)k) (+ unused points up to n).  Answer to U: pick i with
|R_i - U| largest; take one point of each earlier answer of the other cluster outside U (glue), fill with points
of R_i - U.  Check: every triple of answers with empty common intersection has, for EVERY static 4-block cover,
a block of size > T.  Lower bound used (rigorous at finite k): max_g |L_g| >= max_lambda sum_R |R| min_{S in A_R}
lambda(S), minimised over all block configs (tstar.py); an exactly empty X_i frees E_i (mass set to 0).
usage: py -3.14 sim_two_region.py k t c rounds trials seed"""
import sys, random, itertools, math, numpy as np
import tstar
k, t, c, R, trials, seed = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
T = int(t * k); s = math.ceil((2 - c) * k); n = 2 * s + 4 * T      # n > 4T: non-pencil triples cannot be finished
import os; NOGLUE = os.environ.get("NOGLUE") == "1"
rng = random.Random(seed); TAB = tstar.tab(); K = TAB['K']
R1, R2 = set(range(s)), set(range(s, 2 * s)); REG = [R1, R2]
def bound(x, y, z):
    xa, xb, xc = len(y & z) / k, len(x & z) / k, len(x & y) / k
    ea, eb, ec = (len(x) - len(x & y) - len(x & z)) / k, (len(y) - len(x & y) - len(y & z)) / k, (len(z) - len(x & z) - len(y & z)) / k
    m = np.array([xa, xb, xc, ea if xa > 0 else 0, eb if xb > 0 else 0, ec if xc > 0 else 0])
    return (K @ m).max(axis=1).min()
worst = 9; pencils = 0
for tr in range(trials):
    ans, cl = [], []
    def answer(U):
        free = [len(REG[i] - U) for i in (0, 1)]
        i = 0 if free[0] >= free[1] else 1
        glue = set()
        for x, ci in zip(ans, cl):
            if ci != i and not (x & glue) and not NOGLUE:
                cand = sorted((x & REG[ci]) - U); glue.add(rng.choice(cand))
        pool = sorted(REG[i] - U); assert len(pool) >= k - len(glue), 'covering fails'
        B = glue | set(rng.sample(pool, k - len(glue)))
        assert len(B) == k and not (B & U)
        ans.append(B); cl.append(i)
    answer(set())
    for r in range(R):
        mode = rng.randrange(3)
        if mode == 0 or len(ans) < 2:                      # START: T points of a member (+ rest elsewhere)
            x = rng.choice(ans); u = rng.randint(T // 2, T)
            U = set(rng.sample(sorted(x), min(u, k))); rest = sorted(set().union(*ans) - U)
            U |= set(rng.sample(rest, min(len(rest), T - len(U))))
        elif mode == 1:                                    # DUMP on a pair: core + parts of both private parts
            x, y = rng.sample(ans, 2); core = x & y
            if len(core) > T: core = set(rng.sample(sorted(core), T))
            U = set(core); rest = sorted((x | y) - U); U |= set(rng.sample(rest, min(len(rest), T - len(U))))
        else:                                              # random T-set inside the union of answers
            un = sorted(set().union(*ans)); U = set(rng.sample(un, min(T, len(un))))
        answer(U)
    for x, y, z in itertools.combinations(ans, 3):
        if x & y & z: continue
        pencils += 1; v = bound(x, y, z); worst = min(worst, v)
        if not NOGLUE: assert v * k > T, ('static finish possible?', v, T / k)
print('k=%d T=%d n=%d c=%.3f rounds=%d trials=%d: pencils checked %d, min lower bound on max block %.4f > t=%.4f'
      % (k, T, n, c, R, trials, pencils, worst, T / k))
