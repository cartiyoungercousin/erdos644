"""Independent verifier for PETAL Theorem PS (section 26.2), pooled arena adversary.
Nothing imported from compute/petal5, petal3 or other verify files.

Model (points, bitmask ints):
  ground = R_X (nX) | R_Y (nY) | O (m);  members: k-sets with >= k-d_c points in R_c (class c), rest
  'free' (anywhere), 'pool' (rest in R_c u O), 'exact' (exactly d_c in O, k-d_c in R_c).
  hit_c = n_c - k + d_c + 1 : number of R_c points that meets every class-c member (checked by brute force, tiny).
  Request S, |S| <= T, T < hit_X + hit_Y  =>  a reply exists.
Requester: PS verbatim (petals 1-4 with F u J, centres 5-7 with G_j u (B minus B_j)).
Checks per game: every request <= T, reply in H and avoids S, petals class X, centres class Y, common
intersection of petals empty, centre traces on U pairwise disjoint, seven replies pairwise distinct, and a literal
pair brute force for 2-covers (cross-checked against a membership-type test).
"""
import random, sys, itertools, time
from math import ceil

popc = int.bit_count


def bits(m):
    while m:
        l = m & -m
        yield l.bit_length() - 1
        m ^= l


class Fam:
    def __init__(s, k, nX, nY, dX, dY, m, variant='free'):
        s.k, s.n, s.d, s.m, s.variant = k, (nX, nY), (dX, dY), m, variant
        s.mask = [(1 << nX) - 1, ((1 << nY) - 1) << nX]
        s.O = ((1 << m) - 1) << (nX + nY)
        s.N = nX + nY + m
        s.all = (1 << s.N) - 1
        s.hit = [nX - k + dX + 1, nY - k + dY + 1]

    def is_class(s, R, c):
        k, d = s.k, s.d[c]
        if popc(R) != k or popc(R & s.mask[c]) < k - d:
            return False
        if s.variant == 'pool':
            return (R & s.mask[1 - c]) == 0
        if s.variant == 'exact':
            return popc(R & s.O) == d and popc(R & s.mask[c]) == k - d
        return True

    def in_H(s, R):
        return s.is_class(R, 0) or s.is_class(R, 1)

    def allowed(s, c, avail):
        if s.variant == 'pool':
            return avail & (s.mask[c] | s.O)
        return avail


# ---------------------------------------------------------------- adversary
NF = 12


class Adv:
    """Priority-genome adversary; genome[i] = weight vector for reply i, cls[i] in {0,1,2(random)}."""

    def __init__(s, fam, genome, cls, noise, rng):
        s.f, s.g, s.cls, s.noise, s.rng = fam, genome, cls, noise, rng

    def reply(s, S, replies, requests, i):
        f, k = s.f, s.f.k
        avail = f.all & ~S
        opts = []
        for c in (0, 1):
            al = f.allowed(c, avail)
            need = k - f.d[c]
            if popc(al & f.mask[c]) < need or popc(al) < k:
                continue
            if f.variant == 'exact' and popc(avail & f.O) < f.d[c]:
                continue
            opts.append(c)
        if not opts:
            return None
        pref = s.cls[i]
        if pref in opts:
            c = pref
        else:
            c = s.rng.choice(opts)
        al = f.allowed(c, avail)
        # per-point features
        N = f.N
        mult = [0] * N; same = [0] * N; oth = [0] * N; leak = [0] * N
        for (R, rc) in replies:
            for p in bits(R):
                mult[p] += 1
                if rc == c: same[p] += 1
                else: oth[p] += 1
                if not (f.mask[rc] >> p) & 1:
                    leak[p] += 1
        reqd = [0] * N
        for Sr in requests:
            for p in bits(Sr): reqd[p] = 1
        nr = len(replies)
        nc = sum(1 for (_, rc) in replies if rc == c)
        w = s.g[i]
        rng = s.rng
        sc = {}
        for p in bits(al):
            inRc = (f.mask[c] >> p) & 1
            isO = (f.O >> p) & 1
            isOther = (f.mask[1 - c] >> p) & 1
            inR0 = (f.mask[0] >> p) & 1
            v = (w[0] * mult[p] + w[1] * same[p] + w[2] * (1 if nr and mult[p] == nr else 0)
                 + w[3] * (1 if nc and same[p] == nc else 0)
                 + w[4] * reqd[p] + w[5] * isO + w[6] * isOther + w[7] * inRc + w[8] * leak[p]
                 + w[9] * (1 if inR0 and mult[p] > 0 else 0) + w[10] * oth[p] + w[11] * (1 if mult[p] == 0 else 0)
                 + rng.random() * s.noise)
            sc[p] = v
        need = k - f.d[c]
        inR = sorted((p for p in bits(al & f.mask[c])), key=lambda p: -sc[p])
        R = 0
        for p in inR[:need]:
            R |= 1 << p
        rest_pool = al & ~R
        if f.variant == 'exact':
            rest_pool &= f.O
        rest = sorted(bits(rest_pool), key=lambda p: -sc[p])
        for p in rest[:k - need]:
            R |= 1 << p
        if popc(R) != k or not f.is_class(R, c) or (R & S):
            return None
        return R, c


def rand_genome(rng, mode):
    g = []
    for i in range(7):
        if mode == 0:
            w = [rng.choice([-6, -2, 0, 2, 6]) for _ in range(NF)]
        elif mode == 1:
            w = [rng.gauss(0, 3) for _ in range(NF)]
        else:
            w = [rng.choice([-9, 0, 9]) if rng.random() < .4 else 0 for _ in range(NF)]
        g.append(w)
    cls = [rng.choice([0, 1, 2]) for _ in range(7)]
    return g, cls


def mutate(g, cls, rng):
    g = [list(w) for w in g]; cls = list(cls)
    for _ in range(rng.choice([1, 2, 4])):
        i = rng.randrange(7); j = rng.randrange(NF)
        g[i][j] = rng.choice([-9, -6, -2, 0, 2, 6, 9]) if rng.random() < .5 else g[i][j] + rng.gauss(0, 2)
    if rng.random() < .2:
        cls[rng.randrange(7)] = rng.choice([0, 1, 2])
    return g, cls


# handcrafted extremes: petals leak into fresh outside points (max |B|); centres put their d_Y outside-R_Y
# points on earlier petal points of R_X (max trace), or reuse leak points (try to share outside points)
def hand_genomes():
    out = []
    z = lambda: [0.0] * NF
    for leakkind in ('pool', 'other', 'both'):
        for share in (-5, 0, 5):
            g = []
            for i in range(7):
                w = z()
                w[7] = 1.0                       # prefer own arena for the leak? (rest chosen by same score)
                if i < 4:
                    w[0] = -3 if share <= 0 else 3           # fresh vs overlapping petals
                    w[5] = 6 if leakkind in ('pool', 'both') else -6
                    w[6] = 6 if leakkind in ('other', 'both') else -6
                    w[7] = -8                    # leaks pushed outside R
                    w[8] = share                 # reuse earlier leak points (or avoid)
                    w[11] = 4 if share <= 0 else -4
                else:
                    w[0] = 2; w[9] = 8; w[8] = 8 if share >= 0 else -8; w[7] = -8
                    w[5] = 3; w[6] = 3
                g.append(w)
            out.append((g, [2] * 7))
    return out


# ---------------------------------------------------------------- requester
class Over(Exception): pass


def pick(rng, mask, cnt, mode):
    ps = list(bits(mask))
    if mode == 'low': sel = ps[:cnt]
    elif mode == 'high': sel = ps[::-1][:cnt]
    else: sel = rng.sample(ps, cnt)
    r = 0
    for p in sel: r |= 1 << p
    return r


def two_cover_literal(sets, lim=2500):
    U = 0
    for R in sets: U |= R
    pts = list(bits(U))
    mem = {}
    for p in pts:
        t = 0
        for i, R in enumerate(sets):
            if (R >> p) & 1: t |= 1 << i
        mem[p] = t
    full = (1 << len(sets)) - 1
    lit = False
    if len(pts) <= lim:
        for a in range(len(pts)):
            ta = mem[pts[a]]
            if ta == full: lit = True; break
            for b in range(a + 1, len(pts)):
                if ta | mem[pts[b]] == full: lit = True; break
            if lit: break
    types = sorted(set(mem.values()))
    typ = any(t == full for t in types) or any(types[i] | types[j] == full for i in range(len(types)) for j in range(i + 1, len(types)))
    # types of two different points may be equal -> need multiplicity for pair of same type
    cnt = {}
    for t in mem.values(): cnt[t] = cnt.get(t, 0) + 1
    typ = typ or any(c >= 2 and (t | t) == full for t, c in cnt.items())
    if len(pts) <= lim: assert lit == typ, "cover test mismatch"
    return typ


def play(fam, T, X, adv, rng, fill='random', verbose=False):
    """PS verbatim. Returns dict of outcome flags."""
    k = fam.k; Y = 1 - X
    mX, mY = fam.mask[X], fam.mask[Y]
    hitX, hitY = fam.hit[X], fam.hit[Y]
    dX, dY = fam.d[X], fam.d[Y]
    b = T - hitY
    res = dict(flags=[], maxreq=0, covers=False, reqs=[])
    def flag(s): res['flags'].append(s)
    replies = []; requests = []
    def ask(S, label, cls):
        sz = popc(S)
        res['maxreq'] = max(res['maxreq'], sz); res['reqs'].append((label, sz))
        if sz > T:
            flag('OVER %s %d>%d' % (label, sz, T)); raise Over
        r = adv.reply(S, replies, requests, len(replies))
        requests.append(S)
        if r is None:
            flag('NOREPLY %s (premise: tau>T?)' % label); raise Over
        R, c = r
        if not fam.in_H(R) or (R & S) or popc(R) != k:
            flag('BADREPLY ' + label); raise Over
        if not fam.is_class(R, cls):
            flag('WRONGCLASS %s (reply not class %d)' % (label, cls)); raise Over
        replies.append((R, cls))
        return R
    try:
        I = None; pet = []
        for i in range(4):
            if I is None:
                F = pick(rng, mY, hitY, fill); J = 0
            else:
                IY = I & mY
                if popc(IY) > hitY: flag('IY>hitY'); raise Over
                F = IY | pick(rng, mY & ~IY, hitY - popc(IY), fill)
                Iout = I & ~mY
                J = pick(rng, Iout, min(b, popc(Iout)), fill) if Iout else 0
            R = ask(F | J, 'petal%d' % (i + 1), X)
            pet.append(R)
            I = R if I is None else (I & R)
        if I: flag('PETALS COMMON INTERSECTION NONEMPTY (%d)' % popc(I)); raise Over
        U = 0
        for R in pet: U |= R
        B = U & ~mX
        if popc(B) > 4 * dX: flag('|B|>4dX')
        bp = list(bits(B)); rng.shuffle(bp)
        parts = [0, 0, 0]
        for idx, p in enumerate(bp): parts[idx % 3] |= 1 << p
        Zprev = 0; cen = []; traces = []
        for j in range(3):
            ZX = Zprev & mX
            g = max(hitX, popc(ZX))
            G = ZX | pick(rng, mX & ~ZX, g - popc(ZX), fill)
            S = G | (B & ~parts[j])
            R = ask(S, 'centre%d' % (j + 1), Y)
            cen.append(R)
            tr = R & U
            for t2 in traces:
                if t2 & tr: flag('TRACES INTERSECT on U');
            traces.append(tr); Zprev |= tr
        sets = pet + cen
        if len(set(sets)) < 7: flag('DUPLICATE replies (%d distinct)' % len(set(sets)))
        if two_cover_literal(sets): res['covers'] = True; flag('2-COVER EXISTS')
    except Over:
        pass
    return res


def run_family(fam, T, X, games, rng, fill='random', climb=True, tag=''):
    stats = dict(games=0, over=0, covers=0, noreply=0, wrong=0, flags=set(), maxreq=0, trace_viol=0, dup=0)
    def evalg(g, cls, nz, seed):
        r = random.Random(seed)
        adv = Adv(fam, g, cls, nz, r)
        return play(fam, T, X, adv, r, fill)
    def record(res):
        stats['games'] += 1
        stats['maxreq'] = max(stats['maxreq'], res['maxreq'])
        for fl in res['flags']:
            key = fl.split(' ')[0]
            stats['flags'].add(fl if key in ('OVER', 'NOREPLY') else key)
        if any(f.startswith('OVER') for f in res['flags']): stats['over'] += 1
        if res['covers']: stats['covers'] += 1
        if any(f.startswith('NOREPLY') for f in res['flags']): stats['noreply'] += 1
        if any(f.startswith('WRONG') or f.startswith('PETALS') or f.startswith('BAD') for f in res['flags']): stats['wrong'] += 1
        if any(f.startswith('TRACES') for f in res['flags']): stats['trace_viol'] += 1
        if any(f.startswith('DUP') for f in res['flags']): stats['dup'] += 1
    pool = []
    for g, c in hand_genomes():
        pool.append((g, c, 0.5))
    while len(pool) < max(12, games // 6):
        g, c = rand_genome(rng, rng.randrange(3)); pool.append((g, c, rng.choice([0.3, 1, 3])))
    scored = []
    for g, c, nz in pool:
        res = evalg(g, c, nz, rng.randrange(10**9)); record(res)
        scored.append((res['maxreq'] + 1000 * len(res['flags']), g, c, nz))
    scored.sort(key=lambda x: -x[0])
    best = scored[:6]
    while stats['games'] < games:
        sc0, g0, c0, nz0 = rng.choice(best)
        g1, c1 = mutate(g0, c0, rng) if climb else rand_genome(rng, 1)
        res = evalg(g1, c1, nz0, rng.randrange(10**9)); record(res)
        sc1 = res['maxreq'] + 1000 * len(res['flags'])
        if sc1 >= best[-1][0]:
            best.append((sc1, g1, c1, nz0)); best.sort(key=lambda x: -x[0]); best = best[:6]
    return stats


# ---------------------------------------------------------------- parameter solving
def feasible_hits(k, T, dX, dY):
    """hit_X choices (hit_Y = T+1-hit_X) satisfying PS (a),(b) and hit_Y >= dX, in integer points."""
    out = []
    B = 4 * dX; sealB = B - B // 3
    for hX in range(1, T + 1):
        hY = T + 1 - hX
        b = T - hY
        if b * 3 < k: continue
        if hY < dX: continue
        if max(hX, 2 * dY) + sealB > T: continue
        out.append(hX)
    return out


def mkfam(k, T, X, hX, dX, dY, m, variant):
    # classes indexed 0,1 ; class X is `X`; hits[X]=hX
    hits = [0, 0]; hits[X] = hX; hits[1 - X] = T + 1 - hX
    d = [0, 0]; d[X] = dX; d[1 - X] = dY
    n = [hits[c] - 1 + k - d[c] for c in (0, 1)]
    return Fam(k, n[0], n[1], d[0], d[1], m, variant)


def tau_bruteforce(fam):
    """exact min transversal of the whole family H (all members), tiny instances only"""
    mem = [sum(1 << p for p in c) for c in itertools.combinations(range(fam.N), fam.k)]
    mem = [R for R in mem if fam.in_H(R)]
    for s in range(1, fam.N + 1):
        for S in itertools.combinations(range(fam.N), s):
            m = sum(1 << p for p in S)
            if all(R & m for R in mem): return s
    return None


def tiny_exhaustive(k, T, X, hX, dX, dY, m, variant, prefixes, rng):
    """Random prefixes of replies (uniformly random valid member), final reply exhaustive over ALL members,
    plus level-6 sampled; strategy PS verbatim."""
    fam = mkfam(k, T, X, hX, dX, dY, m, variant)
    mem = [sum(1 << p for p in c) for c in itertools.combinations(range(fam.N), k)]
    mem = [R for R in mem if fam.in_H(R)]
    bad = 0; games = 0; overs = 0
    class Oracle:
        def __init__(s): s.choices = []
        def reply(s, S, replies, requests, i):
            cand = [R for R in mem if not (R & S)]
            if not cand: return None
            if i == 6 and s.final is not None:
                R = s.final(cand)
            else:
                R = rng.choice(cand)
            return R, (0 if fam.is_class(R, 0) and not fam.is_class(R, 1) else 1 if fam.is_class(R, 1) and not fam.is_class(R, 0) else rng.choice([0, 1]))
    # simpler: run the whole game with random choices, record sets; then for the last request enumerate
    for _ in range(prefixes):
        orc = Oracle(); orc.final = None
        r = random.Random(rng.randrange(10**9))
        # play up to the last request, capturing it
        captured = {}
        class Stop(Exception): pass
        class Orc2(Oracle):
            def reply(s, S, replies, requests, i):
                if i == 6:
                    captured['S'] = S; captured['replies'] = list(replies); raise Stop
                return Oracle.reply(s, S, replies, requests, i)
        o2 = Orc2(); o2.final = None
        try:
            res = play(fam, T, X, o2, r, 'random')
        except Stop:
            res = None
        if res is not None:
            if any(f.startswith('OVER') for f in res['flags']): overs += 1
            elif res['flags']: bad += 1; print('FLAGS', res['flags'])
            games += 1
            continue
        S = captured['S']; reps = [R for (R, c) in captured['replies']]
        cand = [R for R in mem if not (R & S)]
        Y = 1 - X
        for R in cand:
            games += 1
            if not fam.is_class(R, Y):
                bad += 1; print('final reply not class Y', bin(R)); continue
            sets = reps + [R]
            # petals = reps[:4]; U = union; traces disjoint?
            U = 0
            for q in reps[:4]: U |= q
            trs = [q & U for q in reps[4:]] + [R & U]
            for i in range(3):
                for j in range(i + 1, 3):
                    if trs[i] & trs[j]: bad += 1; print('trace intersect')
            if two_cover_literal(sets): bad += 1; print('COVER')
    return dict(members=len(mem), games=games, bad=bad, overs=overs, tau=None)


if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'main'
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    rng = random.Random(seed)
    if mode == 'tau':
        for (k, nX, nY, dX, dY, m, var) in [(4, 5, 6, 1, 1, 2, 'free'), (4, 6, 5, 2, 1, 1, 'free'), (3, 4, 5, 1, 1, 2, 'pool'), (4, 5, 6, 1, 1, 3, 'exact')]:
            f = Fam(k, nX, nY, dX, dY, m, var)
            print('tiny', (k, nX, nY, dX, dY, m, var), 'hitX+hitY =', sum(f.hit), 'brute tau =', tau_bruteforce(f))
    elif mode == 'tiny':
        npref = int(sys.argv[3]) if len(sys.argv) > 3 else 40
        for (k, T, dX, dY, m) in [(6, 6, 1, 1, 3), (6, 6, 1, 1, 6), (7, 7, 1, 1, 3), (6, 7, 1, 2, 2)]:
            for var in ('free', 'pool', 'exact'):
                if var == 'exact' and m < 3: continue
                for X in (0, 1):
                    for hX in feasible_hits(k, T, dX, dY):
                        fam = mkfam(k, T, X, hX, dX, dY, m, var)
                        if var == 'exact' and m < T + 1: 
                            pass  # tau via O may be < T+1: NOREPLY would show as premise failure
                        t0 = time.time()
                        r = tiny_exhaustive(k, T, X, hX, dX, dY, m, var, npref, rng)
                        print((k, T, dX, dY, m), var, 'X=', X, 'hX=', hX, 'N=', fam.N, r, '%.0fs' % (time.time() - t0), flush=True)
    elif mode == 'ctrl':
        # controls: delta above 3t/16 (budget (b) fails), strategy must overrun, adversary reaches it
        games = int(sys.argv[3]) if len(sys.argv) > 3 else 100
        for (k, T) in [(60, 45), (100, 80)]:
            dmax = int((3 * T / k / 16) * k)
            for dd in (dmax, dmax + 1, dmax + 2, dmax + 4):
                best = None
                for hX in range(1, T + 1):
                    if 3 * (hX - 1) >= k and T + 1 - hX >= dd:  # (a) and hit_Y >= dX only
                        fam = mkfam(k, T, 0, hX, dd, dd, k, 'free')
                        st = run_family(fam, T, 0, games, rng, 'random')
                        pred = max(hX, 2 * dd) + 4 * dd - (4 * dd) // 3
                        print((k, T), 'd=', dd, 'hX=', hX, 'predicted centre req', pred, 'over T' if pred > T else 'ok', 'games', st['games'], 'over', st['over'], 'covers', st['covers'], 'maxreq', st['maxreq'], flush=True)
                        break
    else:
        games = int(sys.argv[3]) if len(sys.argv) > 3 else 150
        rows = []
        for (k, T) in [(60, 45), (60, 47), (80, 64), (100, 80), (90, 77)]:
            t = T / k
            dmax = int((3 * t / 16) * k)
            for (dX, dY) in [(dmax, dmax), (dmax, max(1, dmax - 3)), (max(1, dmax // 2), dmax), (dmax - 1, dmax // 2), (dmax, 0 if False else 1)]:
                fh = {}
                for X in (0, 1):
                    hs = feasible_hits(k, T, dX, dY)
                    if not hs:
                        continue
                    # try loosest, tightest, middle hX
                    for hX in sorted(set([hs[0], hs[len(hs) // 2], hs[-1]])):
                        for var, m in (('free', 0), ('free', k), ('pool', k // 2), ('exact', T + 2 * max(dX, dY) + 2)):
                            fam = mkfam(k, T, X, hX, dX, dY, m, var)
                            if var == 'exact' and (popc(fam.O) < max(dX, dY)): continue
                            for fill in ('random', 'low'):
                                st = run_family(fam, T, X, games, rng, fill)
                                row = (k, T, round(t, 3), dX, dY, X, hX, fam.n, var, m, fill, st['games'], st['over'], st['covers'], st['noreply'], st['wrong'], st['trace_viol'], st['dup'], st['maxreq'], sorted(st['flags'])[:3])
                                print(row, flush=True)
