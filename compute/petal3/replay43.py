"""PETAL Part III section 17: exact replay of two 4+3 strategies against the arena adversary A(t, delta) on point sets.
Adversary (two arenas of n = k + T/2 - d points, replies: k-d points in own arena, d in the other):
  colour forced by counting; own part prefers points lying in replies of the other colour (their bands: maximises his trace),
  then points of high multiplicity in his own colour (keeps common points); band prefers points outside as many
  opposite-colour replies as possible and never re-uses an earlier band of his colour.
Strategies:
  blind  = Theorem J' (14.1): Step 1 by running intersections (t/2 from each class), Step 2 forcing 1-c inside one petal
           (c = a0 - 1 point; forcing points taken from the petal's most shared points) plus the observed traces.
  aware  = 12.3: requests placed by arena.
  aware2 = section 20: as aware, but each band point of the petals is requested in exactly two of the three centre requests.
A request that would exceed T is truncated (traces outside the forcing petal are dropped last-in-first-out) and flagged.
After the 7 replies the EXACT 2-cover test is run (all pairs of membership types; a common point counts).
usage: py replay43.py k T d [seeds]
"""
import sys, random, itertools


def game(k, T, d, mode, seed, n=None):
    rnd = random.Random(seed)
    if n is None: n = k + T // 2 - d
    tau = n - (k - d)                              # true exclusion cost of one colour (section 23: arenas need not be tight)
    V = {"A": set(range(n)), "F": set(range(n, 2 * n))}; OTH = {"A": "F", "F": "A"}
    reps = []                                   # (set, colour)
    over = []                                   # budget overruns (points)

    def adversary(S):
        assert len(S) <= T, ("request over budget", len(S), T)
        xa = len(S & V["A"]); xf = len(S & V["F"])
        if xa > tau: c = "F"
        elif xf > tau: c = "A"
        else:
            ca = sum(1 for _, x in reps if x == "A"); cf = len(reps) - ca
            c = "A" if ca <= cf else "F"
        o = OTH[c]
        same = [u for u, x in reps if x == c]; opp = [u for u, x in reps if x != c]
        own = sorted(V[c] - S); rnd.shuffle(own)
        own.sort(key=lambda x: (-sum(1 for u in opp if x in u), -sum(1 for u in same if x in u)))
        E = set(own[:k - d])
        used = set()
        for u in same: used |= (u & V[o])
        pool = sorted(V[o] - S - used); rnd.shuffle(pool)
        pool.sort(key=lambda x: sum(1 for u in opp if x in u))
        if len(pool) < d:
            extra = sorted(V[o] - S - set(pool)); rnd.shuffle(extra); pool += extra
        E |= set(pool[:d])
        assert len(E) == k and not (E & S)
        reps.append((E, c)); return E, c

    def pick(cands, m, forbid=()):
        c = [x for x in cands if x not in forbid]
        return set(c[:m])

    if mode == "blind":
        c_pts = 2 * (k - d) - n - 1
        f_mass = k - c_pts
        quad = None
        for _ in range(12):
            S = set()
            for col in "AF":
                mem = [u for u, x in reps if x == col][:4]
                if mem:
                    I = set.intersection(*mem); lst = sorted(I); rnd.shuffle(lst)
                    S |= set(lst[:min(T // 2, len(lst))])
            adversary(S)
            for col in "AF":
                mem = [u for u, x in reps if x == col][:4]
                if len(mem) == 4 and not set.intersection(*mem): quad = (col, mem)
            if quad: break
        if not quad: return dict(result="no quad")
        col, P = quad; U = set().union(*P)
        allsame = [u for u, x in reps if x == col]
        cents = []
        for j in range(3):
            Z = set()
            for C in cents: Z |= (C & U)
            a = min(range(4), key=lambda i: len(Z - P[i]))
            Xa = P[a]
            inside = sorted(Z & Xa)
            rest = sorted(Xa - Z); rnd.shuffle(rest)
            rest.sort(key=lambda x: -sum(1 for u in allsame if x in u))
            F = set(inside) | set(rest[:max(0, f_mass - len(inside))])
            outside = sorted(Z - Xa)
            room = T - len(F)
            if len(outside) > room: over.append((j + 1, len(F) + len(outside) - T)); outside = outside[:max(room, 0)]
            S = F | set(outside)
            if len(S) > T: S = set(sorted(S)[:T])
            E, c = adversary(S)
            if c == col: return dict(result="forcing failed")
            cents.append(E)
    elif mode == "ap":
        # section 23 (Theorem AP): petals by running intersections (unforced; both colours have tau >= T/2 here),
        # centres forced by tau+1 points of the petals' own arena, petals' other-arena parts sealed twice in three requests.
        quad = None
        for _ in range(12):
            S = set()
            for colr in "AF":
                mem = [u for u, x in reps if x == colr][:4]
                if mem:
                    I = set.intersection(*mem); lst = sorted(I); rnd.shuffle(lst)
                    S |= set(lst[:min(T // 2, len(lst))])
            adversary(S)
            for colr in "AF":
                mem = [u for u, x in reps if x == colr][:4]
                if len(mem) == 4 and not set.intersection(*mem): quad = (colr, mem)
            if quad: break
        if not quad: return dict(result="no quad")
        col, P = quad; o = OTH[col]; cents = []
        bands = set()
        for u in P: bands |= (u & V[o])
        for j in range(3):
            SA = set()
            for C in cents: SA |= (C & V[col])
            fill = sorted(V[col] - SA); rnd.shuffle(fill)
            SA |= set(fill[:max(0, tau + 1 - len(SA))])
            SF = [x for i, x in enumerate(sorted(bands)) if (i % 3) != (j + 2) % 3]
            if len(SA) + len(SF) > T: over.append((j + 1, len(SA) + len(SF) - T)); SF = SF[:T - len(SA)]
            E, c = adversary(SA | set(SF))
            if c == col: return dict(result="forcing failed")
            cents.append(E)
    else:
        col = "A"; P = []
        chunk = (T // 2 - 1) if mode != "ap" else tau
        va = sorted(V["A"])
        for j in range(4):
            S = set()
            for u in P: S |= (u & V["F"])
            fill = sorted(V["F"] - S); rnd.shuffle(fill)
            S |= set(fill[:max(0, (T // 2 + 1 if mode != "ap" else tau + 1) - len(S & V["F"]))])
            S |= set(va[j * chunk:(j + 1) * chunk]) if j < 3 else set(va[-chunk:])
            E, c = adversary(S); assert c == "A"; P.append(E)
        if set.intersection(*P): return dict(result="no quad")
        U = set().union(*P); cents = []
        bandsF = set()
        for u in P: bandsF |= (u & V["F"])
        for j in range(3):
            SA = set()
            for C in cents: SA |= (C & V["A"])
            fill = sorted(V["A"] - SA); rnd.shuffle(fill)
            SA |= set(fill[:max(0, (T // 2 + 1 if mode != "ap" else tau + 1) - len(SA))])
            SF = sorted(bandsF)
            if mode in ("aware2", "ap"):                       # section 20: every band point is requested in two of the three centre requests
                SF = [x for i, x in enumerate(SF) if (i % 3) != (j + 2) % 3]
            room = T - len(SA)
            if len(SF) > room: over.append((j + 1, len(SA) + len(SF) - T)); SF = SF[:room]
            E, c = adversary(SA | set(SF)); assert c == "F"; cents.append(E)
    seven = P + cents
    U7 = set().union(*seven)
    types = {}
    for x in U7:
        m = sum(1 << i for i in range(7) if x in seven[i]); types[m] = types.get(m, 0) + 1
    ms = list(types)
    cover = any((m1 | m2) == 127 for m1 in ms for m2 in ms)
    Uq = set().union(*P)
    tr = [C & Uq for C in cents]
    disjoint = not (tr[0] & tr[1] or tr[0] & tr[2] or tr[1] & tr[2])
    return dict(result="NO 2-COVER (requester wins)" if not cover else "2-cover exists", over=over,
                traces=[len(x) for x in tr], disjoint=disjoint, requests=len(reps))


if __name__ == "__main__":
    k, T, d = map(int, sys.argv[1:4]); seeds = int(sys.argv[4]) if len(sys.argv) > 4 else 5
    for mode in ("blind", "aware", "aware2"):
        res = [game(k, T, d, mode, s) for s in range(seeds)]
        wins = sum(1 for r in res if r["result"].startswith("NO"))
        print("k=%d T=%d d=%d delta=%.4f %-5s wins %d/%d  e.g. %s" % (k, T, d, d / k, mode, wins, seeds, res[0]), flush=True)
