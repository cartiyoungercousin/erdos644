r"""Exact check of Lemma F1 (notes 5.6): for a value map lam: V'' -> F2^3 and fixed region sizes m,
  S(lam)/Mult(m) = E[ prod_x (-1)^<lam(x), Y_x> ]  (Y uniform labelling with counts m),
computed EXACTLY by DP over the remaining counts, against the bound Phi_p(nu)/P_m, where
  Phi_p(nu) = max { prod_u t_u^(n_u/2) : sum_u t_u = 8 sum_v p_v^2, 0 <= t_u <= 1 },   P_m = P(Mult(N, p) = m).
[computed exact: rationals for S, floats for the bound]"""
import itertools, random, math, sys
from fractions import Fraction
from functools import lru_cache

def exact_ratio(lams, m):
    # lams: list of u in 0..7 per point; m: dict v->count (v = 1..7)
    vs = list(range(1, 8)); N = len(lams)
    from collections import defaultdict
    dp = {tuple(m[v] for v in vs): Fraction(1)}
    for x, u in enumerate(lams):
        nd = defaultdict(Fraction)
        for st, val in dp.items():
            tot = sum(st)
            for i, v in enumerate(vs):
                if st[i] == 0: continue
                s = -1 if bin(u & v).count('1') % 2 else 1
                ns = st[:i] + (st[i] - 1,) + st[i + 1:]
                nd[ns] += val * Fraction(st[i], tot) * s
        dp = nd
    return dp[tuple(0 for _ in vs)]

def phi_bound(lams, m):
    N = len(lams); p = [m[v] / N for v in range(1, 8)]
    P2 = 8 * sum(q * q for q in p)
    n = [lams.count(u) for u in range(8)]
    # maximise sum (n_u/2) ln t_u, sum t = P2, t <= 1: water-filling
    act = [u for u in range(8) if n[u] > 0]
    t = {u: 0.0 for u in range(8)}
    capped = set(); budget = P2
    while True:
        free = [u for u in act if u not in capped]
        tot = sum(n[u] for u in free)
        if not free: break
        ok = True
        for u in free:
            t[u] = budget * n[u] / tot
        over = [u for u in free if t[u] > 1]
        if not over: break
        for u in over: capped.add(u); t[u] = 1.0
        budget = P2 - len(capped)
    val = math.exp(sum(n[u] / 2 * math.log(t[u]) for u in act if t[u] > 0)) if all(t[u] > 0 for u in act) else 0.0
    Pm = math.factorial(N) / math.prod(math.factorial(m[v]) for v in range(1, 8)) * math.prod(q ** m[v] for q, v in zip(p, range(1, 8)))
    return val / Pm

rng = random.Random(1)
worst = 0
for trial in range(300):
    mm = rng.choice([1, 2, 3])
    m = {v: mm + rng.randint(0, 1) for v in range(1, 8)}
    N = sum(m.values())
    kind = rng.random()
    if kind < 0.4:      # near-constant: dominant value, few others
        u0 = rng.randrange(8); d = rng.randint(1, max(1, N // 3))
        lams = [u0] * N
        for x in rng.sample(range(N), d): lams[x] = rng.randrange(8)
    else:
        lams = [rng.randrange(8) for _ in range(N)]
    # skip constants (exact value +-1, handled separately)
    if len(set(lams)) == 1: continue
    r = exact_ratio(lams, m); b = phi_bound(lams, m)
    worst = max(worst, abs(float(r)) / b)
    assert abs(float(r)) <= b * (1 + 1e-9), (lams, m, r, b)
print('Lemma F1 bound holds on all trials; max |S|/Mult / bound =', round(worst, 4))
