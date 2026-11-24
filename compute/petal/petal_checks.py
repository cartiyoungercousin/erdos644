"""PETAL.md checks (brute force on real sets).
A: petal lemma / dangerous graph / active set U* / centre criteria (P1-P4) on random small systems.
B: Theorem H strategy (class-blind running intersection, then forced centres with disjoint traces)
   against randomized leaky two-arena adversaries; final 7-tuple checked by brute force.
Usage: py petal_checks.py A | B [games]
"""
import random, itertools, sys

def covers(fam, pts):
    """all 2-covers {x,y} (x<=y allowed equal) of fam within pts"""
    out = []
    for x, y in itertools.combinations_with_replacement(sorted(pts), 2):
        if all((x in E) or (y in E) for E in fam):
            out.append((x, y))
    return out

def gamma(P):
    """dangerous graph of petal set P: pairs x!=y in U with every petal containing x or y"""
    U = set().union(*P)
    ed = [(x, y) for x, y in itertools.combinations(sorted(U), 2)
          if all((x in B) or (y in B) for B in P)]
    act = set()
    for x, y in ed:
        act.add(x); act.add(y)
    return U, ed, act

def checkA(trials=4000, seed=1):
    rng = random.Random(seed); n_ok = 0
    for _ in range(trials):
        n = rng.randint(6, 12); q = rng.randint(2, 6); r = rng.randint(1, 7 - q)
        ground = list(range(n))
        P = [set(rng.sample(ground, rng.randint(2, n - 2))) for _ in range(q)]
        if set.intersection(*P):
            continue
        C = [set(rng.sample(ground, rng.randint(1, n - 1))) for _ in range(r)]
        U, ed, act = gamma(P)
        # activity formula: x active iff petals missing x have a common point
        for x in U:
            miss = [B for B in P if x not in B]
            assert (x in act) == bool(set.intersection(*miss)), "activity formula"
        cov = covers(P + C, ground)
        # P1: every cover is an edge of Gamma, inside U*
        assert all(x != y and x in act and y in act for x, y in cov)
        # P2: cover iff Gamma-edge not missed entirely by any centre
        pred = [(x, y) for x, y in ed if all((x in c) or (y in c) for c in C)]
        assert sorted(pred) == sorted(cov)
        # trace equivalence + monotonicity (replace centres by traces on U*, then pad inside U*)
        Ct = [c & act for c in C]
        assert sorted(covers(P + Ct, ground)) == sorted(cov) if all(Ct) or True else True
        Cp = [c | set(rng.sample(sorted(act), rng.randint(0, len(act)))) if act else c for c in Ct]
        covp = covers(P + Cp, ground)
        assert set(cov) <= set(covp), "monotone"
        # P3: one centre: uncoverable iff C misses U*
        c = C[0]
        assert (len(covers(P + [c], ground)) == 0) == (not (c & act))
        # P4: three centres with pairwise disjoint traces on U* -> uncoverable
        if r >= 3:
            a, b, d = C[0] & act, C[1] & act, C[2] & act
            if not (a & b or a & d or b & d):
                assert not covers(P + C[:3], ground)
        n_ok += 1
    print("check A: %d random systems, all assertions hold" % n_ok)

# ---------------------------------------------------------------- B
def playB(k, T, d, rng, verbose=False):
    N = k + T // 2 - d + 1                      # arena size; tau > T
    AX = set(range(N)); AY = set(range(N, 2 * N)); fresh = [2 * N]
    arena = {'X': AX, 'Y': AY}
    Cmin = 2 * (k - d) - N                      # guaranteed same-class overlap
    replies = {'X': [], 'Y': []}
    order = []
    def adversary(S, style):
        feas = [c for c in 'XY' if len(arena[c] - S) >= k - d]
        assert feas, "request blocked both arenas (should be impossible)"
        if style[0] == 'few' and len(feas) == 2:   # prefer the class with fewer replies
            feas.sort(key=lambda c: len(replies[c]))
            c = feas[0]
        elif style[0] == 'many' and len(feas) == 2:
            feas.sort(key=lambda c: -len(replies[c])); c = feas[0]
        else:
            c = rng.choice(feas)
        avail = list(arena[c] - S)
        deg = lambda x: sum(x in E for E in replies[c])
        rng.shuffle(avail)
        if style[1] == 'hi': avail.sort(key=lambda x: -deg(x))
        m = min(len(avail), k) if style[2] == 'noleak' else k - d
        main = set(avail[:m])
        # leak: unrequested points outside own arena, prefer points of other-class replies / old leaks
        o = 'Y' if c == 'X' else 'X'
        cand = [x for x in set().union(*(replies['X'] + replies['Y']), arena[o]) - arena[c] - S]
        rng.shuffle(cand)
        odeg = lambda x: sum(x in E for E in replies[o]) + 2 * sum(x in E for E in replies[c])
        if style[3] == 'adv': cand.sort(key=lambda x: -odeg(x))
        leak = set(cand[:k - m])
        while len(main) + len(leak) < k:
            leak.add(fresh[0]); fresh[0] += 1
        E = main | leak
        assert len(E) == k and not (E & S)
        return c, E
    style = (rng.choice(['few', 'many', 'rand']), rng.choice(['hi', 'rand']),
             rng.choice(['leak', 'leak', 'noleak']), rng.choice(['adv', 'rand']))
    def classify(E):
        # the requester can recover the class from overlaps with class representatives
        o = [c for c in 'XY' if replies[c] and len(E & replies[c][0]) >= Cmin]
        lo = [c for c in 'XY' if replies[c] and len(E & replies[c][0]) > 2 * d and c not in o]
        assert len(o) <= 1 and not lo, "overlap pattern is not two-class"
        return o[0] if o else None
    nreq = 0
    def take(s, m):
        s = list(s); rng.shuffle(s); return set(s[:m])
    # Step 1: class-blind running intersection
    while True:
        done = [c for c in 'XY' if len(replies[c]) >= 4 and not set.intersection(*replies[c][:4])]
        if done: break
        S = set()
        if replies['X'] and replies['Y']:
            S |= replies['X'][0] & replies['Y'][0]
        b = (T - len(S)) // 2
        for c in 'XY':
            if replies[c]:
                I = set.intersection(*replies[c][:4]) - S
                S |= take(I, b)
        assert len(S) <= T
        c, E = adversary(S, style); nreq += 1
        assert classify(E) in (c, None) and (classify(E) == c or not replies[c])
        replies[c].append(E)
        assert nreq <= 8, "step 1 took more than 8 requests"
    pc = done[0]; P = replies[pc][:4]
    U, ed, act = gamma(P)
    # Step 2: three forced centres of the other class with pairwise disjoint traces on U
    cents = []; Z = set()
    for j in range(3):
        inside = Z & P[0]
        F = inside | take(P[0] - inside, k - Cmin + 1 - len(inside))
        S = F | Z
        assert len(S) <= T, "budget exceeded in step 2: %d > %d" % (len(S), T)
        c, E = adversary(S, style); nreq += 1
        assert c != pc, "forcing failed"
        replies[c].append(E)
        cents.append(E); Z |= (E & U)
    fam = P + cents
    pts = set().union(*fam)
    assert not covers(fam, pts), "7-tuple is 2-coverable"
    return nreq, style

def checkB(games=200, seed=7):
    rng = random.Random(seed); mx = 0
    for (k, T, d) in [(40, 30, 1), (80, 60, 2), (80, 62, 2), (60, 46, 1)]:
        for g in range(games):
            n, st = playB(k, T, d, rng); mx = max(mx, n)
        print("check B: k=%d T=%d leak d=%d: %d games won (7 uncoverable replies), max requests %d"
              % (k, T, d, games, mx))

if __name__ == "__main__":
    if sys.argv[1] == 'A': checkA()
    else: checkB(int(sys.argv[2]) if len(sys.argv) > 2 else 200)
