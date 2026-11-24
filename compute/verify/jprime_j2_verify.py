"""
Independent verifier for PETAL Theorem J' (14.1) and J'' (18.1).  Written from the statements only.

Model (units: k points per reply; request size <= T; reply disjoint from the request).
Class constraints  C(c, mu): same-class overlap >= OX = floor(c k)+1 ; cross overlap <= MU = floor(mu k).
Forcing: a request containing >= K-C points of X_a (K-C = ceil((1-c)k)) leaves reply overlap <= C < OX, so
the reply is not in class X.

Step 1 is run verbatim against a fully legal two-class adversary (ILP over Venn cells).
Step 2 is run verbatim (J' with fixed a / adaptive a ; J'' with rotation) against a *relaxed* adversary
(only: disjoint from request, overlap <= MU with each of the four petals) -- a superset of legal adversaries --
whose trace is chosen by ILP to maximise the later request sizes.  Also run on arbitrary petal configurations
(ILP vertices over Venn-cell counts), a superset of what Step 1 can produce.
Final: exact 2-cover test of the seven sets (mask pairs).
"""
import sys, random, itertools, math

from _hs import MIP
def ilp(avail, ge, le, w, k, wf):
    m = MIP()
    x = [m.var(0, avail[i], w[i]) for i in range(len(avail))]
    f = m.var(0, k, wf)
    m.row(x + [f], k, k)
    for idx, rhs in ge: m.row([x[i] for i in idx], rhs, 1e9)
    for idx, rhs in le: m.row([x[i] for i in idx], 0, rhs)
    sol = m.solve()
    if sol is None: return None
    return sol[:len(x)], sol[len(x)]

class Ctr:
    n = 0
    @classmethod
    def fresh(cls, m):
        s = set(range(cls.n, cls.n + m)); cls.n += m; return s

def groups_of(replies, requested):
    g = {}
    for p in set().union(*replies) if replies else set():
        if p in requested: continue
        sig = tuple(p in R for R in replies)
        g.setdefault(sig, []).append(p)
    keys = list(g.keys())
    return keys, [g[s] for s in keys]

def build_reply(replies, requested, k, ge_rep, le_rep, wfun, wfresh, rng, OX, MU):
    """reply as set. ge_rep: indices of replies with overlap>=OX ; le_rep: overlap<=MU"""
    keys, pts = groups_of(replies, requested)
    avail = [len(p) for p in pts]
    ge = [([i for i, s in enumerate(keys) if s[r]], OX) for r in ge_rep]
    le = [([i for i, s in enumerate(keys) if s[r]], MU) for r in le_rep]
    w = [wfun(keys[i]) for i in range(len(keys))]
    res = ilp(avail, ge, le, w, k, wfresh)
    if res is None: return None
    cnt, f = res
    out = set()
    for i, c in enumerate(cnt):
        out |= set(rng.sample(pts[i], c))
    out |= Ctr.fresh(f)
    return out

def two_cover(sets):
    allp = set().union(*sets)
    masks = set()
    for p in allp:
        m = 0
        for i, S in enumerate(sets):
            if p in S: m |= 1 << i
        masks.add(m)
    full = (1 << len(sets)) - 1
    ml = list(masks)
    for a in ml:
        for b in ml:
            if a | b == full: return True
    return False

# ---------------------------------------------------------------- Step 1 (verbatim)
def step1(k, T, C, MU, rng, pattern, objmode):
    OX = C + 1
    K_ = k
    R = []; cls = []; requests = []
    for step in range(7):
        # requests: min(T//2,|I|) of I^A and of I^B
        S = set()
        for c_ in 'AB':
            mem = [R[i] for i in range(len(R)) if cls[i] == c_][:4]
            if mem:
                I = set.intersection(*mem)
                S |= set(rng.sample(sorted(I), min(T // 2, len(I))))
        assert len(S) <= T
        requests.append(S)
        want = pattern[step]
        if not R: want = 'A'
        done = None
        for c_ in ([want] + [x for x in 'AB' if x != want]):
            if c_ == 'B' and not R: continue
            ge = [i for i in range(len(R)) if cls[i] == c_]
            le = [i for i in range(len(R)) if cls[i] != c_]
            if c_ == 'B' and not ge and 'A' not in cls: continue
            memc = [R[i] for i in ge][:4]
            I = set.intersection(*memc) if memc else set()
            if objmode == 'keepI':
                wf = lambda s, I=I, R=R: sum(1 for i, b in enumerate(s) if b) * 0.0
                # weight points in I (all A-members contain it): detect via sig all ge true
                geset = ge
                wfun = lambda s, geset=geset: 1.0 if (geset and all(s[i] for i in geset[:4])) else 0.0
                wfresh = 0.0
            elif objmode == 'fresh':
                wfun = lambda s: 0.0; wfresh = 1.0
            elif objmode == 'overlap':
                wfun = lambda s: 1.0; wfresh = 0.0
            else:
                ws = {}
                def wfun(s, ws=ws):
                    if s not in ws: ws[s] = rng.random()
                    return ws[s]
                wfresh = rng.random()
            rep = build_reply(R, S, k, ge, le, wfun, wfresh, rng, OX, MU)
            if rep is not None:
                done = (rep, c_); break
        if done is None:
            return None  # adversary has no legal reply
        R.append(done[0]); cls.append(done[1])
    nA = cls.count('A'); nB = cls.count('B')
    big = 'A' if nA >= 4 else 'B'
    petals = [R[i] for i in range(7) if cls[i] == big][:4]
    return petals, requests, (nA, nB)

# ---------------------------------------------------------------- Step 2 (verbatim)
def mult(p, petals): return sum(p in X for X in petals)

def singles(petals):
    return [{p for p in petals[a] if mult(p, petals) == 1} for a in range(4)]

def step2(petals, k, T, C, MU, thm, rng, objmode, filler, adaptive_a=False, fixed_a=0):
    """returns dict.  thm in 'Jp','Jpp'."""
    OX = C + 1
    Fsize = k - C
    sing = singles(petals)
    U = set().union(*petals)
    if thm == 'Jpp':
        order = sorted(range(4), key=lambda a: len(sing[a]))
        a3 = order[0]
        rest = [a for a in range(4) if a != a3]
        if rng.random() < 0.5: rng.shuffle(rest)
        arot = [rest[0], rest[1], a3]
        if objmode == 'adv_perm':  # try random permutation too, not assuming smallest single last (should still be ok? not claimed)
            pass
    Zs = []; Cs = []; reqs = []; costs = []
    for j in range(3):
        Zprev = set().union(*Zs) if Zs else set()
        if thm == 'Jp':
            if adaptive_a and Zs:
                a = min(range(4), key=lambda b: len(Zprev - petals[b]))
            else:
                a = fixed_a
            must = Zprev & petals[a]
        else:
            a = arot[j]
            must = (Zprev & petals[a]) | sing[a]
        Fs = max(Fsize, len(must))
        pool = sorted(petals[a] - must)
        if filler == 'single': pool.sort(key=lambda p: (mult(p, petals), rng.random()))
        elif filler == 'multi': pool.sort(key=lambda p: (-mult(p, petals), rng.random()))
        else: rng.shuffle(pool)
        F = set(must) | set(pool[:Fs - len(must)])
        S = F | (Zprev - petals[a])
        reqs.append(S); costs.append(len(S))
        if len(S) > T:
            return dict(ok=False, reason='budget', j=j, size=len(S), costs=costs)
        assert len(F & petals[a]) >= Fsize
        # adversary (relaxed): disjoint from S, <=MU with each petal.  Check class-X infeasible by arithmetic
        assert k - len(F) <= C < OX
        # objective
        if thm == 'Jp':
            def wfun(s, a=a):
                inU = any(s[:4])
                return (1.0 if (inU and not s[a]) else 0.0) + 0.01 * rng.random()
        else:
            nxt = arot[j + 1:]
            def wfun(s, nxt=nxt):
                if not any(s[:4]): return 0.0
                v = 0.0
                for q, b in enumerate(nxt):
                    v += (2.0 if b == arot[2] else 1.0) * (0.0 if s[b] else 1.0)
                if not nxt: v = rng.random()
                return v + 0.01 * rng.random()
        if objmode == 'random':
            ws = {}
            def wfun(s, ws=ws):
                if s not in ws: ws[s] = rng.random()
                return ws[s]
        elif objmode == 'maxU':
            wfun = lambda s: (1.0 if any(s[:4]) else 0.0) + 0.01 * rng.random()
        reps = list(petals)
        rep = build_reply(reps, S, k, [], [0, 1, 2, 3], wfun, 0.0, rng, OX, MU)
        if rep is None:
            return dict(ok=False, reason='advstuck', j=j)
        assert not (rep & S) and len(rep) == k
        Cs.append(rep); Zs.append(rep & U)
        if thm == 'Jpp' and j >= 1:
            for i in range(j):
                aj = arot[j]
                assert len(Zs[i] - petals[aj]) <= 2 * MU, ("2mu claim", len(Zs[i] - petals[aj]))
        if thm == 'Jpp':
            assert len(Zs[j]) <= 3 * MU, ("3mu claim", len(Zs[j]))
            assert not (Zs[j] & sing[arot[j]])
    # pairwise disjoint traces
    for i in range(3):
        for j in range(i + 1, 3):
            assert not (Zs[i] & Zs[j])
    cover = two_cover(petals + Cs)
    return dict(ok=True, cover=cover, costs=costs)

# ---------------------------------------------------------------- arbitrary petal configurations
CELLS = [c for r in (1, 2, 3) for c in itertools.combinations(range(4), r)]

def random_config(k, C, rng):
    OX = C + 1
    m = MIP()
    n = {}
    for c in CELLS:
        wt = rng.random() * (3 if len(c) == 1 and rng.random() < .5 else 1)
        n[c] = m.var(0, k, wt)
    for a in range(4): m.row([n[c] for c in CELLS if a in c], k, k)
    for a, b in itertools.combinations(range(4), 2):
        m.row([n[c] for c in CELLS if a in c and b in c], OX, 1e9)
    sol = m.solve()
    if sol is None: return None
    petals = [set() for _ in range(4)]
    for c in CELLS:
        pts = Ctr.fresh(sol[n[c]])
        for a in c: petals[a] |= pts
    return petals

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    games = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    rng = random.Random(seed)
    params = [  # (label, k, T, C, MU, thm)
        ("t.75 c.5  Jpp bdry", 600, 450, 300, 37, 'Jpp'),
        ("t.75 c.5  Jp  bdry", 600, 450, 300, 25, 'Jp'),
        ("t.75 c.6  Jpp bdry", 600, 450, 360, 52, 'Jpp'),
        ("t.75 c.6  Jp  bdry", 600, 450, 360, 35, 'Jp'),
        ("t.8  c.55 Jpp bdry", 600, 480, 330, 52, 'Jpp'),
        ("t.8  c.55 Jp  bdry", 600, 480, 330, 35, 'Jp'),
    ]
    summary = {}
    for (lab, k, T, C, MU, thm) in params:
        assert (k - C) + (4 if thm == 'Jpp' else 6) * MU <= T, lab
        stats = dict(games=0, wins=0, budget_fail=0, cover=0, stuck=0, maxcost3=0, step1_none=0)
        for g in range(games):
            Ctr.n = 0
            if g % 2 == 0:
                s1 = step1(k, T, C, MU, rng, rng.choice(['AAAAAAA', 'AABABAB', 'ABABABA', 'AAAABBB', 'ABBBAAA', 'BAAAABB', 'AABBAAB']).replace('B', 'B'),
                           rng.choice(['keepI', 'fresh', 'overlap', 'random']))
                if s1 is None:
                    stats['step1_none'] += 1; continue
                petals = s1[0]
                for X, Y in itertools.combinations(petals, 2): assert len(X & Y) >= C + 1
                assert not set.intersection(*petals)
            else:
                petals = random_config(k, C, rng)
                if petals is None: continue
            for variant in range(2 if thm == 'Jp' else 1):
                for filler in ('random', 'single', 'multi'):
                    for om in ('adv', 'maxU', 'random'):
                        r = step2(petals, k, T, C, MU, thm, rng, om, filler, adaptive_a=bool(variant), fixed_a=rng.randrange(4))
                        stats['games'] += 1
                        if not r['ok']:
                            stats['budget_fail' if r['reason'] == 'budget' else 'stuck'] += 1
                            print("!!! FAIL", lab, r)
                            continue
                        stats['wins'] += 1
                        stats['maxcost3'] = max(stats['maxcost3'], r['costs'][2])
                        if r['cover']:
                            stats['cover'] += 1; print("!!! COVER", lab, r)
        stats['T'] = T; stats['bound'] = (k - C) + (4 if thm == 'Jpp' else 6) * MU
        summary[lab] = stats
        print(lab, stats, flush=True)
    return summary

if __name__ == "__main__":
    main()
