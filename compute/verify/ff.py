"""Lemma FF (23.1): equal-size sets, pairwise overlaps >= m (i.e. > c with c = m - 1/2... any c<m).
Claim in points: tau <= k - m - pi(X) + 1 for every member X (the +1 is the epsilon).  Exact tau by HiGHS (pulp)."""
import random, itertools, sys


def tau(fam, N):
    fam = [sorted(f) for f in fam]
    best = [N]
    def rec(chosen, rem):
        if len(chosen) >= best[0]: return
        if not rem: best[0] = len(chosen); return
        s = min(rem, key=len)
        for x in s:
            rec(chosen + [x], [f for f in rem if x not in f])
    rec([], fam)
    return best[0]

def check(fam, N, k):
    m = min(len(a & b) for a, b in itertools.combinations(fam, 2))
    t = tau(fam, N)
    worst = None
    for i, X in enumerate(fam):
        others = set().union(*[Y for j, Y in enumerate(fam) if j != i])
        pi = len(X - others)
        bound = k - m - pi + 1
        if worst is None or bound < worst[0]: worst = (bound, i, pi)
    return t, m, worst

rnd = random.Random(1)
viol = 0; tests = 0; tight = 0
for trial in range(1500):
    k = rnd.randint(4, 9); N = rnd.randint(k + 1, 2 * k + 3); q = rnd.randint(2, 9)
    # try to generate near-clustered family: random sets, then keep those with pairwise overlap >= m
    m0 = rnd.randint(1, k - 1)
    fam = []
    for _ in range(200):
        s = frozenset(rnd.sample(range(N), k))
        if all(len(s & a) >= m0 for a in fam): fam.append(s)
        if len(fam) >= q: break
    if len(fam) < 2: continue
    t, m, (bound, i, pi) = check(fam, N, k)
    tests += 1
    if t > bound: viol += 1; print("VIOLATION", fam, t, bound)
    if t == bound: tight += 1
print("random families", tests, "violations", viol, "tight", tight)
# adversarial hill-climb: maximise tau - bound
def score(fam, N, k):
    t, m, (b, i, pi) = check(fam, N, k); return t - b
best = -99
for rep in range(60):
    k = rnd.randint(5, 8); N = rnd.randint(k + 2, 2 * k); q = rnd.randint(3, 7)
    fam = []
    while len(fam) < q:
        fam.append(frozenset(rnd.sample(range(N), k)))
    cur = score(fam, N, k)
    for it in range(150):
        f2 = list(fam); j = rnd.randrange(q); s = set(f2[j]); a = rnd.choice(list(s)); b = rnd.choice([x for x in range(N) if x not in s]); s.remove(a); s.add(b); f2[j] = frozenset(s)
        sc = score(f2, N, k)
        if sc >= cur: fam, cur = f2, sc
    best = max(best, cur)
print("max (tau - bound) over hill-climbed families (<=0 required):", best)
# the 'single-mass form is false' example: complete family on ground set of size N=2k-m? all k-subsets
k, N = 6, 10   # all 6-subsets of 10 points: min overlap 2 ; tau = N-k+1 = 5
fam = [frozenset(s) for s in itertools.combinations(range(N), k)]
t, m, w = check(fam, N, k); print("complete family k=6,N=10: tau", t, "m", m, "FF bound", w, " (tau = k-m+... )")
