r"""FABLE_C section 5, Proposition NP (near-pool, collinear repair): plain-code check of the strategy.
Instance k = 140, T = 110, n = 280 (N = 2, eps = 1/28, omega*k = 30), core Y of 30 points, V' = 250 points.
Every reply must contain all but at most eta points of Y.  Proposition NP needs eta <= 4*eps*k/7 = 20/7, so eta = 2.
Her play: Fano classes on V' (sizes below), requests in order i = 1..7:
   S_i = L_i  u  R_i,   R_i = union over lines {a,b,i} with a,b < i of (M_a n M_b),  M_a = Y \ K_a.
The adversary (several heuristics, all legal: K contains S, |K| = c, |Y \ K| <= eta) answers; at the end every pair
of V must be covered.  Also run with eta = 3 > 20/7 against the 'common miss' adversary to see the request overflow.
[computed exact: each game is an exact check; the adversaries are heuristic, the proof is by hand]"""
import random, itertools, sys
LINES = [(1, 2, 3), (1, 4, 5), (1, 6, 7), (2, 4, 6), (2, 5, 7), (3, 4, 7), (3, 5, 6)]
k, T, n = 140, 110, 280; c = n - k; ycore = 30; nprime = n - ycore
r_ = {i: sum(1 for L in LINES if max(L) == i) for i in range(1, 8)}


def plan(eta):
    cap = {i: T - eta * r_[i] for i in range(1, 8)}
    # even line sizes <= cap with sum 3 n'
    ell = {i: cap[i] - (cap[i] % 2) for i in range(1, 8)}
    over = sum(ell.values()) - 3 * nprime
    if over < 0: return None
    i = 1
    while over > 0:
        ell[i] -= 2; over -= 2; i = i % 7 + 1
    v = {L: (sum(ell[i] for i in L) // 2) - sum(ell.values()) // 6 for L in LINES}
    assert sum(ell.values()) == 3 * nprime and all(x >= 0 for x in v.values()) and sum(v.values()) == nprime
    return ell, v


def game(eta, adv, rng):
    pl = plan(eta)
    if pl is None: return 'no plan'
    ell, v = pl
    Y = list(range(ycore)); pts = list(range(ycore, n)); rng.shuffle(pts)
    cls = {}; p = 0
    for L in LINES: cls[L] = pts[p:p + v[L]]; p += v[L]
    Lset = {i: set(x for L in LINES if i in L for x in cls[L]) for i in range(1, 8)}
    K = {}; M = {}
    common = set(rng.sample(Y, eta))
    for i in range(1, 8):
        R = set()
        for L in LINES:
            if max(L) == i:
                a, b = [j for j in L if j != i]; R |= M[a] & M[b]
        S = Lset[i] | R
        assert len(S) <= T, ('request too large', len(S))
        free = [y for y in Y if y not in S]
        if adv == 'common': miss = set(y for y in common if y not in S)
        elif adv == 'random': miss = set(rng.sample(free, min(eta, len(free))))
        elif adv == 'line':    # miss points already missed by an earlier member that shares a line with i (first two of a line)
            cand = [y for y in free if any(y in M[a] for L in LINES if i in L for a in L if a < i)]
            rng.shuffle(cand); miss = set(cand[:eta])
            rest = [y for y in free if y not in miss]; miss |= set(rng.sample(rest, min(eta - len(miss), len(rest))))
        elif adv == 'heavy':   # miss the points with the most misses so far
            cand = sorted(free, key=lambda y: (-sum(1 for a in M if y in M[a]), rng.random())); miss = set(cand[:eta])
        Kset = S | (set(Y) - miss)
        rest = [x for x in range(ycore, n) if x not in Kset]; rng.shuffle(rest)
        Kset |= set(rest[:c - len(Kset)]); assert len(Kset) == c and len(set(Y) - Kset) <= eta
        K[i] = Kset; M[i] = set(Y) - Kset
    typ = {}
    for x in range(n): typ.setdefault(frozenset(i for i in K if x in K[i]), 0)
    ts = list(typ)
    return all(a & b for a in ts for b in ts)


if __name__ == '__main__':
    rng = random.Random(644); games = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    print('plan eta=2:', plan(2))
    for adv in ('common', 'random', 'line', 'heavy'):
        res = [game(2, adv, rng) for _ in range(games)]
        print(f"eta = 2, adversary {adv}: {sum(1 for x in res if x is True)}/{games} games end in a good seven")
    print('eta = 3 (> 4 eps k / 7 = 20/7): plan exists?', plan(3) is not None,
          '| count: 7T - 7*eta =', 7 * T - 21, 'vs 3n\' =', 3 * nprime)
