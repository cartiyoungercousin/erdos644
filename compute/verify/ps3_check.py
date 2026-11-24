"""Independent finite-k replay of PETAL Theorem PS3 (28.2). Own code (my ps_check / ps2_check helpers only).

Requester (28.2 verbatim, integers; X = class of petals, hit numbers (hX,hY), hX+hY = T+1, w = T-hY):
  petals 1-4: F_i u W_i, F_i in R_Y with |F_i| = hY, F_4 contains the common R_Y points of petals 1-3, request 4 also holds the
  pool common points of petals 1-3.  W_1, W_2 private blocks of size w; p = nX - 3w; W_3 = P u S0, W_4 = P' u (S0 minus s points)
  with |P| = |P'| = p, |S0| = w - p, s = number of points of P1 n P2 n P3 outside R_X.
  centres: petal 1 is D, petal 2 is S in request 5, petal 3 in 6, petal 4 in 7; G_5 >= T_2 n R_X; G_6 >= (T_3 n R_X) u Z_5; G_7 >= (T_4 n R_X) u Z_5 u Z_6
  (all of size >= hX); B patterns chosen by an integer program (rules of 28.2) on the actual B points minimising the largest request.
"""
import itertools, random, sys, time
import highspy
from ps_check import (Fam, Adv, bits, popc, pick, two_cover_literal, rand_genome, mutate, hand_genomes, mkfam)
from ps2_check import StructAdv
from ps3_lp import TYPES, allowed3, vertices_Q

INF = highspy.kHighsInf


def solve_patterns3(counts, Gb):
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    h.addVar(0.0, INF); h.changeColCost(0, 1.0)
    cols = []
    for J, n in counts.items():
        if n == 0: continue
        for P in allowed3(J):
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
    return round(sol[0]), {cols[c]: round(sol[1 + c]) for c in range(len(cols)) if round(sol[1 + c]) > 0}


class Over(Exception): pass


def play3(fam, T, adv, rng, fill='random'):
    X = 0; Y = 1; k = fam.k
    mX, mY = fam.mask[X], fam.mask[Y]
    hX, hY = fam.hit[X], fam.hit[Y]; dX, dY = fam.d[X], fam.d[Y]
    res = dict(flags=[], maxreq=0, covers=False, reqs=[], pred=None)
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
        w = T - hY
        p = fam.n[0] - 3 * w
        if p < 0 or w - p < 0: flag('PARAM p=%d sigma=%d' % (p, w - p)); raise Over
        rxp = list(bits(mX))
        if fill == 'random': rng.shuffle(rxp)
        elif fill == 'high': rxp = rxp[::-1]
        def mk(lst):
            m = 0
            for q in lst: m |= 1 << q
            return m
        W1 = mk(rxp[:w]); W2 = mk(rxp[w:2 * w])
        Pp = rxp[2 * w:2 * w + p]; Pq = rxp[2 * w + p:2 * w + 2 * p]; S0l = rxp[2 * w + 2 * p:]
        assert len(S0l) == w - p, (len(S0l), w, p)
        Pm, Pqm = mk(Pp), mk(Pq); S0 = mk(S0l)
        W3 = Pm | S0
        pet = []
        for i in range(4):
            F = None
            if i == 0 or i == 1 or i == 2:
                F = pick(rng, mY, hY, fill); Wi = [W1, W2, W3][i]; extra = 0
                R = ask(F | Wi, 'petal%d' % (i + 1), X)
            else:
                cm = pet[0] & pet[1] & pet[2] & ~mX
                cmY, cmO = cm & mY, cm & ~mY
                if popc(cmY) > hY: flag('common R_Y > hY'); raise Over
                F = cmY | pick(rng, mY & ~cmY, hY - popc(cmY), fill)
                s = popc(cm)
                shr = list(bits(S0));
                if fill == 'random': rng.shuffle(shr)
                if s > len(shr): flag('s > sigma'); raise Over
                W4 = Pqm | (S0 & ~mk(shr[:s]))
                R = ask(F | cmO | W4, 'petal4', X)
            pet.append(R)
        for i, Wi in enumerate([W1, W2, W3]):
            if (pet[i] & mX) != (mX & ~Wi): flag('STRUCT Pi n RX != RX - Wi (i=%d)' % (i + 1))
        if pet[0] & pet[1] & pet[2] & pet[3]: flag('PETALS COMMON INTERSECTION NONEMPTY'); raise Over
        U = pet[0] | pet[1] | pet[2] | pet[3]; B = U & ~mX
        typ = {p_: frozenset(i + 1 for i in range(4) if (pet[i] >> p_) & 1) for p_ in bits(U)}
        counts = {J: 0 for J in TYPES}; bypt = {J: [] for J in TYPES}
        for q in bits(B): counts[typ[q]] += 1; bypt[typ[q]].append(q)
        def cell(a):
            c = frozenset({1, 2, 3, 4}) - {a}; m = 0
            for q in bits(U & mX):
                if typ[q] == c: m |= 1 << q
            return m
        Tc = {a: cell(a) for a in (2, 3, 4)}
        Gb = {5: max(hX, popc(Tc[2])), 6: max(hX, popc(Tc[3]) + dY), 7: max(hX, popc(Tc[4]) + 2 * dY)}
        L, asg = solve_patterns3(counts, Gb)
        res['pred'] = L
        if L > T: flag('OVERPRED planned max request %d>%d' % (L, T)); raise Over
        pat = {}
        for J, pts in bypt.items():
            pts = list(pts); rng.shuffle(pts); q = 0
            for (J2, P), c in asg.items():
                if J2 != J: continue
                for x in pts[q:q + c]: pat[x] = P
                q += c
            assert q == len(pts)
        Zprev = 0
        for j in (5, 6, 7):
            must = {5: Tc[2], 6: Tc[3] | (Zprev & mX), 7: Tc[4] | (Zprev & mX)}[j]
            g = max(hX, popc(must))
            G = must | pick(rng, mX & ~must, g - popc(must), fill)
            Bj = 0
            for x, P in pat.items():
                if j in P: Bj |= 1 << x
            R = ask(G | Bj, 'centre%d' % (j - 4), Y)
            Zprev |= R & U
        sets = [r for r, _ in replies]
        if two_cover_literal(sets): res['covers'] = True; flag('2-COVER EXISTS')
    except Over:
        pass
    return res


class Struct3(StructAdv):
    """petals 1-3: leak exactly d (groups + singles); petal 4: leak given by the target (>= d - s), R_X part chosen adversarially."""
    def __init__(self, fam, target, genome, cls, rng, r4mode='shrunk', singles_in='RY'):
        super().__init__(fam, target, genome, cls, rng, 'rand', singles_in)
        self.r4m = r4mode
    def reply(self, S, replies, requests, i):
        if i != 3: return StructAdv.reply(self, S, replies, requests, i)
        f = self.f; k = f.k; d = f.d[0]
        avail = f.all & ~S
        l4t = sum(n for J, n in self.target.items() if 4 in J)
        rx = list(bits(avail & f.mask[0]))
        # R_X part size between k-d and min(k, |avail RX|)
        lmin = k - len(rx) if len(rx) < k else 0
        l4 = max(min(d, l4t), k - len(rx), 0)
        l4 = min(l4, d)
        part_n = k - l4
        P1, P2, P3 = replies[0][0], replies[1][0], replies[2][0]
        def key(q):
            m = ((P1 >> q) & 1) + ((P2 >> q) & 1) + ((P3 >> q) & 1)
            if self.r4m == 'shrunk': return (-(1 if ((P1 >> q) & 1 and (P2 >> q) & 1 and not (P3 >> q) & 1) else 0), self.rng.random())
            if self.r4m == 'other': return ((1 if ((P1 >> q) & 1 and (P2 >> q) & 1 and not (P3 >> q) & 1) else 0), self.rng.random())
            return (self.rng.random(),)
        rx.sort(key=key)
        part = rx[:part_n]
        R = 0
        for q in part: R |= 1 << q
        leak = []
        for J, pts in self.groups.items():
            if 4 in J:
                for q in pts:
                    if (avail >> q) & 1 and len(leak) < l4: leak.append(q)
        for q in leak: R |= 1 << q
        cand = [q for q in (bits(avail & f.mask[1]) if (self.singles_in == 'RY' and f.variant != 'pool') else self.free_pool) if (avail >> q) & 1 and q not in self.used and not (R >> q) & 1]
        self.rng.shuffle(cand)
        extra = cand[:l4 - len(leak)]
        if len(extra) < l4 - len(leak):
            more = [q for q in self.free_pool if (avail >> q) & 1 and q not in self.used and q not in extra and not (R >> q) & 1]
            self.rng.shuffle(more); extra += more[:l4 - len(leak) - len(extra)]
        for q in extra: R |= 1 << q; self.used.add(q)
        if popc(R) != k or not f.is_class(R, 0) or (R & S): return None
        return R, 0


def targets_Q(d):
    V = vertices_Q()
    return [{J: int(x * d) for J, x in zip(TYPES, v)} for v in V]


def run3(k, T, d, variant, gp, rng, order=None, generic=40):
    st = dict(games=0, over=0, overpred=0, covers=0, noreply=0, struct=0, wrong=0, param=0, maxreq=0, other=set())
    def rec(res):
        st['games'] += 1; st['maxreq'] = max(st['maxreq'], res['maxreq'])
        for fl in res['flags']:
            w = fl.split(' ')[0]
            key = {'OVER': 'over', 'OVERPRED': 'overpred', '2-COVER': 'covers', 'NOREPLY': 'noreply', 'STRUCT': 'struct', 'PARAM': 'param'}.get(w)
            if key: st[key] += 1
            elif w in ('WRONGCLASS', 'PETALS', 'BADREPLY'): st['wrong'] += 1
            else: st['other'].add(fl)
    tg = targets_Q(d)
    hs = order or [((T + 1) // 2, T + 1 - (T + 1) // 2), (T + 1 - (T + 1) // 2, (T + 1) // 2)]
    for (hX, hY) in hs:
        fam = mkfam(k, T, 0, hX, d, d, 12 * d + 20, variant)
        gens = hand_genomes()
        for t_ in tg:
            for rep in range(gp):
                g, c = gens[rng.randrange(len(gens))] if rng.random() < .6 else rand_genome(rng, rng.randrange(3))
                adv = Struct3(fam, t_, g, c, rng, rng.choice(['shrunk', 'other', 'rand']), rng.choice(['RY', 'pool']))
                rec(play3(fam, T, adv, random.Random(rng.randrange(10**9)), rng.choice(['random', 'low', 'high'])))
        best = []
        for gi in range(generic):
            if best and rng.random() < .6:
                g0, c0, nz0 = rng.choice(best)[1:]; g, c = mutate(g0, c0, rng)
            else:
                g, c = rand_genome(rng, rng.randrange(3)); nz0 = 0.5
            adv = Adv(fam, g, c, nz0, rng)
            res = play3(fam, T, adv, random.Random(rng.randrange(10**9)), rng.choice(['random', 'low']))
            rec(res); best.append((res['maxreq'], g, c, nz0)); best.sort(key=lambda x: -x[0]); best = best[:6]
    return st


if __name__ == '__main__':
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    gp = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    rng = random.Random(seed)
    cfgs = [(40, 30, 8), (80, 60, 16), (120, 90, 24), (100, 78, 21), (80, 62, 17), (60, 45, 12), (100, 80, 19), (50, 40, 9), (80, 60, 12)]
    if len(sys.argv) > 3 and sys.argv[3] == 'ctrl':
        cfgs = [(40, 30, 9), (80, 60, 17), (80, 60, 18), (100, 78, 24), (100, 80, 22), (20, 15, 4)]
    for (k, T, d) in cfgs:
        for var in ('free', 'pool'):
            t0 = time.time()
            r = run3(k, T, d, var, gp, rng)
            print((k, T, d, round(T / k, 3), 'delta*k=%.2f' % ((T / k / 2 - 1 / 6) * k), var), {a: b for a, b in r.items() if a != 'other'}, sorted(r['other'])[:2], '%.0fs' % (time.time() - t0), flush=True)
