"""Independent finite-k replay of PETAL Theorem PS2 (27.2), pooled arena adversary, delta < t/4.
Own code (reuses only my own ps_check.py model/adversary/2-cover test and ps2_lp.py type/pattern rules; nothing from petal5).

Requester (27.2 verbatim, integers):
  petals 1..4: request F_i u W_i ; F_i in R_Y, |F_i| = max(hit_Y, |R_Y-parts of earlier petals|), contains them;
     W_1..W_3 disjoint blocks of R_X of size T - hit_Y, W_4 = R_X minus them; request 4 also holds the pool points
     common to petals 1-3.
  centres 5..7: S-petal a in {1,2,3} chosen after the petals by an integer program on the actual B points that
     minimises the largest request; G_5 contains T_a n R_X, G_6 contains T_4 n R_X and the R_X-trace of centre 5,
     G_7 the R_X-traces of 5 and 6, all of size >= hit_X; request j = G_j u {B points with j in their pattern}.
Checks: every request <= T; every reply in H; petals class X; centres class Y; petal common intersection empty; structure
facts used by the proof (P_i n R_X = R_X - W_i for i <= 3; R_Y-parts disjoint); literal all-pairs 2-cover test.
"""
import itertools, random, sys, time
import highspy
from ps_check import (Fam, Adv, bits, popc, pick, two_cover_literal, rand_genome, mutate, hand_genomes, mkfam)
from ps2_lp import TYPES, allowed


def solve_patterns(counts, a, Gb):
    """counts: {J: n_J}.  min L with load_j + Gb[j] <= L.  Returns (L, {(J,P): int})."""
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    INF = highspy.kHighsInf
    h.addVar(0.0, INF); h.changeColCost(0, 1.0)
    cols = []
    for J, n in counts.items():
        if n == 0: continue
        for P in allowed(J, a):
            h.addVar(0.0, float(n)); cols.append((J, P))
            h.changeColIntegrality(len(cols), highspy.HighsVarType.kInteger)
    for J, n in counts.items():
        if n == 0: continue
        idx = [1 + c for c, (J2, P) in enumerate(cols) if J2 == J]
        h.addRow(n, n, len(idx), idx, [1.0] * len(idx))
    for j in (5, 6, 7):
        idx = [1 + c for c, (J2, P) in enumerate(cols) if j in P]
        h.addRow(-INF, -Gb[j], len(idx) + 1, [0] + idx, [-1.0] + [1.0] * len(idx))
    h.run()
    sol = h.getSolution().col_value
    L = round(sol[0])
    return L, {cols[c]: round(sol[1 + c]) for c in range(len(cols)) if round(sol[1 + c]) > 0}


class Over(Exception): pass


def play2(fam, T, adv, rng, fill='random'):
    X = 0; Y = 1
    k = fam.k; mX, mY = fam.mask[X], fam.mask[Y]
    hX, hY = fam.hit[X], fam.hit[Y]; dX, dY = fam.d[X], fam.d[Y]
    res = dict(flags=[], maxreq=0, covers=False, reqs=[], a=None)
    def flag(s): res['flags'].append(s)
    replies = []; requests = []
    def ask(S, label, cls):
        sz = popc(S); res['maxreq'] = max(res['maxreq'], sz); res['reqs'].append((label, sz))
        if sz > T: flag('OVER %s %d>%d' % (label, sz, T)); raise Over
        r = adv.reply(S, replies, requests, len(replies))
        requests.append(S)
        if r is None: flag('NOREPLY %s' % label); raise Over
        R, c = r
        if not fam.in_H(R) or (R & S) or popc(R) != k: flag('BADREPLY ' + label); raise Over
        if not fam.is_class(R, cls): flag('WRONGCLASS ' + label); raise Over
        replies.append((R, cls)); return R
    try:
        om = T - hY
        rxp = list(bits(mX));
        if fill == 'random': rng.shuffle(rxp)
        elif fill == 'high': rxp = rxp[::-1]
        W = []
        pos = 0
        for i in range(3):
            m = 0
            for p in rxp[pos:pos + om]: m |= 1 << p
            W.append(m); pos += om
        m = 0
        for p in rxp[pos:]: m |= 1 << p
        W.append(m)
        pet = []
        for i in range(4):
            Zp = 0
            for P in pet: Zp |= P & mY
            F = Zp | pick(rng, mY & ~Zp, max(hY, popc(Zp)) - popc(Zp), fill)
            extra = 0
            if i == 3:
                cm = pet[0] & pet[1] & pet[2]
                extra = cm & ~mX & ~mY
            R = ask(F | W[i] | extra, 'petal%d' % (i + 1), X)
            pet.append(R)
        # structural facts used by the proof
        for i in range(3):
            if (pet[i] & mX) != (mX & ~W[i]): flag('STRUCT Pi n RX != RX - Wi (i=%d)' % (i + 1))
        for i in range(4):
            for j in range(i + 1, 4):
                if pet[i] & pet[j] & mY: flag('STRUCT R_Y parts of petals intersect')
        I = pet[0] & pet[1] & pet[2] & pet[3]
        if I: flag('PETALS COMMON INTERSECTION NONEMPTY'); raise Over
        U = pet[0] | pet[1] | pet[2] | pet[3]
        B = U & ~mX
        if popc(B) > 4 * dX: flag('|B|>4dX')
        # types of B points and triple cells
        typ = {}
        for p in bits(U):
            typ[p] = frozenset(i + 1 for i in range(4) if (pet[i] >> p) & 1)
        counts = {J: 0 for J in TYPES}
        bypt = {J: [] for J in TYPES}
        for p in bits(B):
            counts[typ[p]] += 1; bypt[typ[p]].append(p)
        def Tcell(a):
            c = frozenset({1, 2, 3, 4}) - {a}
            m = 0
            for p in bits(U & mX):
                if typ[p] == c: m |= 1 << p
            return m
        Tc = {a: Tcell(a) for a in (1, 2, 3, 4)}
        if popc(Tc[4]) != popc(W[3]): flag('STRUCT T4 n RX != W4')
        for a in (1, 2, 3):
            if popc(Tc[a]) > om: flag('STRUCT T_a n RX > block')
        best = None
        for a in (1, 2, 3):
            Gb = {5: max(hX, popc(Tc[a])), 6: max(hX, popc(Tc[4]) + dY), 7: max(hX, 2 * dY)}
            L, asg = solve_patterns(counts, a, Gb)
            if best is None or L < best[0]: best = (L, a, asg)
        L, a, asg = best
        res['a'] = a; res['pred'] = L
        if L > T: flag('OVERPRED predicted max centre request %d>%d' % (L, T)); raise Over
        # patterns -> points
        pat = {}
        for J, pts in bypt.items():
            pts = list(pts); rng.shuffle(pts); q = 0
            for (J2, P), c in asg.items():
                if J2 != J: continue
                for p in pts[q:q + c]: pat[p] = P
                q += c
            assert q == len(pts)
        Zprev = 0; cen = []; traces = []
        for j in (5, 6, 7):
            if j == 5: must = Tc[a]
            elif j == 6: must = Tc[4] | (Zprev & mX)
            else: must = Zprev & mX
            g = max(hX, popc(must))
            G = must | pick(rng, mX & ~must, g - popc(must), fill)
            Bj = 0
            for p, P in pat.items():
                if j in P: Bj |= 1 << p
            R = ask(G | Bj, 'centre%d' % (j - 4), Y)
            cen.append(R); tr = R & U; traces.append(tr); Zprev |= tr
        sets = [r for r, _ in replies]
        if two_cover_literal(sets): res['covers'] = True; flag('2-COVER EXISTS')
    except Over:
        pass
    return res


# ------------------------------------------------------------ structured adversary
class StructAdv:
    """petals: leak structure given by target counts per type (pool groups for multi-types, fresh singles otherwise);
    centres: delegated to a priority genome adversary (class Y, traces into U n R_X)."""
    def __init__(self, fam, target, genome, cls, rng, r4mode='rand', singles_in='RY'):
        self.f, self.target, self.rng, self.r4 = fam, target, rng, r4mode
        self.singles_in = singles_in
        self.cen = Adv(fam, genome, cls, 0.5, rng)
        self.groups = {}
        pool = list(bits(fam.O)); rng.shuffle(pool); q = 0
        for J, n in target.items():
            if len(J) >= 2 and n > 0:
                self.groups[J] = pool[q:q + n]; q += n
        self.free_pool = pool[q:]
        self.used = set()
    def reply(self, S, replies, requests, i):
        f = self.f; k = f.k
        if i >= 4: return self.cen.reply(S, replies, requests, i)
        c = 0; d = f.d[0]
        avail = f.all & ~S
        # R_X part
        rx = list(bits(avail & f.mask[0]))
        need = k - d
        if len(rx) < need: return None
        if i < 3:
            part = rx[:]  # exactly need points (R_X minus W_i)
            if len(part) != need: part = self.rng.sample(rx, need) if len(rx) > need else part
        else:
            if self.r4 == 'rand': part = self.rng.sample(rx, need)
            elif self.r4 == 'low': part = sorted(rx)[:need]
            else: part = sorted(rx)[::-1][:need]
        R = 0
        for p in part: R |= 1 << p
        leak = []
        for J, pts in self.groups.items():
            if (i + 1) in J:
                for p in pts:
                    if (avail >> p) & 1 and len(leak) < d: leak.append(p)
        for p in leak: R |= 1 << p
        # fill with fresh singles
        cand = []
        if self.singles_in == 'RY' and f.variant != 'pool':
            cand = [p for p in bits(avail & f.mask[1]) if p not in self.used]
        else:
            cand = [p for p in self.free_pool if (avail >> p) & 1 and p not in self.used]
        self.rng.shuffle(cand)
        need2 = d - len(leak)
        # single count target for this petal: use target singles first then any
        extra = cand[:need2]
        if len(extra) < need2:
            extra += [p for p in bits(avail & ~f.mask[0]) if p not in self.used and p not in extra and (R >> p) & 1 == 0][:need2 - len(extra)]
        for p in extra: R |= 1 << p; self.used.add(p)
        if popc(R) != k or not f.is_class(R, 0) or (R & S): return None
        return R, 0


def vertex_targets(d):
    from ps2_lp import vertices
    from fractions import Fraction
    V = [v for v in vertices() if any(v)]
    out = []
    for v in V:
        t = {J: int(x * d) for J, x in zip(TYPES, v)}
        out.append(t)
    return out


def fam_params(k, T, d):
    hs = [((T + 1) // 2, T + 1 - (T + 1) // 2), (T + 1 - (T + 1) // 2, (T + 1) // 2)]
    return hs


def run(k, T, d, variant, games_per, rng, dY=None, extra_generic=60):
    dY = d if dY is None else dY
    stats = dict(games=0, over=0, overpred=0, covers=0, noreply=0, struct=0, wrong=0, maxreq=0, other=set())
    hs = fam_params(k, T, d)
    targets = vertex_targets(d)
    def rec(res):
        stats['games'] += 1; stats['maxreq'] = max(stats['maxreq'], res['maxreq'])
        for fl in res['flags']:
            w = fl.split(' ')[0]
            if w == 'OVER': stats['over'] += 1
            elif w == 'OVERPRED': stats['overpred'] += 1
            elif w == '2-COVER': stats['covers'] += 1
            elif w == 'NOREPLY': stats['noreply'] += 1
            elif w == 'STRUCT': stats['struct'] += 1
            elif w in ('WRONGCLASS', 'PETALS', 'BADREPLY'): stats['wrong'] += 1
            else: stats['other'].add(fl)
    for (hX, hY) in hs:
        m = 12 * d + 20
        fam = mkfam(k, T, 0, hX, d, dY, m, variant)
        if variant == 'pool' and False: continue
        gens = [hg for hg in hand_genomes()]
        for tg in targets:
            for rep in range(games_per):
                g, c = gens[rng.randrange(len(gens))] if rng.random() < .6 else rand_genome(rng, rng.randrange(3))
                adv = StructAdv(fam, tg, g, c, rng, rng.choice(['rand', 'low', 'high']), rng.choice(['RY', 'pool']))
                rec(play2(fam, T, adv, random.Random(rng.randrange(10**9)), rng.choice(['random', 'low', 'high'])))
        # generic genome adversaries (all seven replies), random + hill climbing on the largest request
        best = []
        for gi in range(extra_generic):
            if best and rng.random() < .6:
                g0, c0, nz0 = rng.choice(best)[1:]
                g, c = mutate(g0, c0, rng)
            else:
                g, c = rand_genome(rng, rng.randrange(3)); nz0 = 0.5
            adv = Adv(fam, g, c, nz0, rng)
            res = play2(fam, T, adv, random.Random(rng.randrange(10**9)), rng.choice(['random', 'low']))
            rec(res)
            best.append((res['maxreq'], g, c, nz0)); best.sort(key=lambda x: -x[0]); best = best[:6]
    return stats


if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    gp = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    rng = random.Random(seed)
    cfgs = [(40, 30, 6), (40, 30, 7), (80, 60, 12), (80, 60, 14), (80, 60, 15), (100, 78, 18), (100, 78, 19),
            (50, 40, 9), (120, 90, 22), (60, 45, 10), (60, 45, 11), (100, 80, 19), (150, 117, 28)]
    if len(sys.argv) > 3 and sys.argv[3] == 'ctrl':
        cfgs = [(40, 30, 8), (80, 60, 16), (80, 60, 18), (16, 12, 3), (100, 78, 22)]
    for (k, T, d) in cfgs:
        for var in ('free', 'pool'):
            t0 = time.time()
            st = run(k, T, d, var, gp, rng)
            print((k, T, d, round(T / k, 3), round(d / k, 4), 'T/4=%.2f' % (T / 4), var), {kk: v for kk, v in st.items() if kk != 'other'}, sorted(st['other'])[:3], '%.0fs' % (time.time() - t0), flush=True)
