"""CORE Part VI: the two-stage game (replies 3 and 4, discard allowed), first-order model, units k = 1.

State after replies 1, 2: co-type masses O = K1&K2 (o), A, B (c - o each), g (N - 2c + o).
Stage 3: she requests S3 (mass t over the 4 types), he adds D3 (mass omega over unrequested mass).
Stage 4: the same over the 8 types.
Value of a position:  need = min over readings R of need_R, where a reading is a kept set R of >= 2 replies with a
Fano labelling (which triples are pencils), and
    need_R = min sum_f u_f  s.t. every point's final co-type contains a pencil, the 7 - |R| future lines have
             mass <= t + u_f (0 <= u_f <= omega)      [an LP in the type masses]
= the useful dump she still needs from future replies if she keeps R.  need_R <= 0 is an outright static win.
Baseline (two free replies, nothing gained) is omega - 4 eps.  She minimises, he maximises.
Usage: py twostage.py t N o [seed] [iters]      (o = |K1 & K2|)
"""
import itertools, sys, random, json, time
import highspy

PL = [frozenset(p) for p in [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]]
INF = 9.0


def patterns(r):
    """canonical injections [r] -> labels, one per concurrency pattern"""
    seen = {}
    for phi in itertools.permutations(range(7), r):
        key = frozenset(frozenset(i for i in range(r) if phi[i] in P) for P in PL if sum(phi[i] in P for i in range(r)) == 3)
        if key not in seen: seen[key] = phi
    return list(seen.values())


class Reading:
    def __init__(self, R, phi, t, om, pen=None):
        self.R, self.phi = R, phi
        r = len(R); F = [f for f in range(7) if f not in phi]
        self.hs = list(range(1 << r))
        h = highspy.Highs(); h.setOptionValue("output_flag", False); h.setOptionValue("presolve", "off")
        nrow = (1 << r) + len(F)
        inf = highspy.kHighsInf
        for hh in self.hs: h.addRow(0.0, 0.0, 0, [], [])
        for _ in F: h.addRow(-inf, t, 0, [], [])
        self.cols = []
        for hh in self.hs:
            base = frozenset(phi[i] for i in range(r) if hh >> i & 1)
            for k in range(len(F) + 1):
                for E in itertools.combinations(range(len(F)), k):
                    H = base | frozenset(F[e] for e in E)
                    if any(P <= H for P in PL):
                        idx = [hh] + [(1 << r) + e for e in E]
                        h.addCol(0.0, 0.0, inf, len(idx), idx, [1.0] * len(idx)); self.cols.append((hh, E))
        for e in range(len(F)): h.addCol(1.0, 0.0, om, 1, [(1 << r) + e], [-1.0])
        if pen is not None:                                   # overflow beyond omega at cost pen (keeps the LP feasible)
            for e in range(len(F)): h.addCol(pen, 0.0, inf, 1, [(1 << r) + e], [-1.0])
        self.h = h; self.r = r; self.F = F

    def need(self, mu, want_dual=False):
        """mu: masses of the 2^r projected types"""
        for hh in self.hs: self.h.changeRowBounds(hh, mu[hh], mu[hh])
        self.h.run()
        st = self.h.getModelStatus()
        if st != highspy.HighsModelStatus.kOptimal: return (INF, None) if want_dual else INF
        v = self.h.getInfo().objective_function_value
        if want_dual: return v, list(self.h.getSolution().row_dual)
        return v


class Game:
    def __init__(self, t, N, pen=None):
        self.t, self.N = t, N; self.c = N - 1; self.om = N - 1 - t; self.base = self.om - 4 * (t - 0.75)
        self.readings = []
        for r in (2, 3, 4):
            for R in itertools.combinations(range(4), r):
                for phi in patterns(r): self.readings.append(Reading(R, phi, t, self.om, pen))
        self.nlp = 0

    def proj(self, m, R):
        mu = [0.0] * (1 << len(R))
        for J, v in m.items():
            hh = 0
            for i, x in enumerate(R):
                if J >> x & 1: hh |= 1 << i
            mu[hh] += v
        return mu

    def need(self, m, with4=None, stop_below=None, nrep=4):
        """min over readings among the first nrep replies (with4: True = only readings containing reply 4)"""
        best = INF; arg = None
        for rd in self.readings:
            if max(rd.R) >= nrep: continue
            if with4 is True and 3 not in rd.R: continue
            if with4 is False and 3 in rd.R: continue
            self.nlp += 1
            v = rd.need(self.proj(m, rd.R))
            if v < best: best, arg = v, rd
            if stop_below is not None and best < stop_below - 1e-9: break
        return best, arg

    @staticmethod
    def step(m, s, d, bit):
        m2 = {}
        for J, v in m.items():
            inn = s.get(J, 0.0) + d.get(J, 0.0)
            if inn > 1e-12: m2[J | bit] = m2.get(J | bit, 0.0) + inn
            if v - inn > 1e-12: m2[J] = m2.get(J, 0.0) + v - inn
        return m2

    def dump_menu(self, m, s, rich=False):
        """vertex-type dumps: all of omega' on one type (spill to the next types of a priority list), pairs half-half"""
        free = {J: m[J] - s.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}
        om = self.N - 1 - sum(s.values())
        types = sorted(free)
        out = []
        def fill(order, amounts=None):
            d = {}; left = om
            if amounts:
                for J, a in amounts:
                    x = min(a, free[J], left); d[J] = d.get(J, 0.0) + x; left -= x
            for J in order:
                if left <= 1e-12: break
                x = min(free[J] - d.get(J, 0.0), left)
                if x > 0: d[J] = d.get(J, 0.0) + x; left -= x
            return d
        tot = sum(free.values())
        out.append({J: om * v / tot for J, v in free.items()})                      # proportional
        for J in types:
            rest = [K for K in types if K != J]
            out.append(fill([J] + sorted(rest, key=lambda K: -bin(K).count("1"))))
            if rich: out.append(fill([J] + sorted(rest, key=lambda K: bin(K).count("1"))))
        for J, K in itertools.combinations(types, 2):
            out.append(fill([J, K] + [L for L in types if L not in (J, K)], [(J, om / 2), (K, om / 2)]))
            if rich:
                out.append(fill([J, K] + [L for L in types if L not in (J, K)], [(J, om / 4), (K, 3 * om / 4)]))
                out.append(fill([J, K] + [L for L in types if L not in (J, K)], [(J, 3 * om / 4), (K, om / 4)]))
        if rich:
            for tr in itertools.combinations(types, 3):
                out.append(fill(list(tr) + [L for L in types if L not in tr], [(J, om / 3) for J in tr]))
        # dedupe
        seen = set(); res = []
        for d in out:
            key = tuple(sorted((J, round(v, 9)) for J, v in d.items() if v > 1e-12))
            if key not in seen: seen.add(key); res.append(d)
        return res

    def value4(self, m3, s4, vprev, incumbent=None, rich=False, order=None):
        """max over his stage-4 menu of min over readings containing reply 4 (capped by vprev).
        incumbent: she already has a request with this value; return early (>= incumbent) if some dump reaches it."""
        menu = self.dump_menu(m3, s4, rich)
        if order: menu = sorted(menu, key=lambda d: -order.get(self.dkey(d), 0))
        worst = -INF; wd = None
        for d in menu:
            m4 = self.step(m3, s4, d, 8)
            v, _ = self.need(m4, with4=True, stop_below=worst if worst > -INF else None)
            v = min(v, vprev)
            if v > worst: worst, wd = v, d
            if incumbent is not None and worst >= incumbent - 1e-9: break
        if order is not None and wd is not None: order[self.dkey(wd)] = order.get(self.dkey(wd), 0) + 1
        return worst, wd

    @staticmethod
    def dkey(d): return tuple(sorted(J for J, v in d.items() if v > 1e-9))

    def norm(self, m, s, tgt=None):
        """clip a request to availability and rescale to mass t"""
        tgt = self.t if tgt is None else tgt
        s = {J: max(0.0, min(v, m[J])) for J, v in s.items() if J in m}
        for _ in range(60):
            tot = sum(s.values())
            if abs(tot - tgt) < 1e-12: break
            if tot > tgt:
                f = tgt / tot; s = {J: v * f for J, v in s.items()}
            else:
                room = {J: m[J] - s.get(J, 0.0) for J in m}; R = sum(room.values())
                if R <= 1e-12: break
                add = min(1.0, (tgt - tot) / R)
                s = {J: s.get(J, 0.0) + add * room[J] for J in m}
        return s

    def cand4(self, m3):
        """structured stage-4 requests: unions of whole types (greedy by a priority order), then to mass t"""
        types = sorted(m3); out = []
        orders = set()
        for perm in itertools.permutations(types, min(4, len(types))): orders.add(perm)
        for od in orders:
            s = {}; left = self.t
            for J in od:
                x = min(m3[J], left); s[J] = x; left -= x
            if left > 1e-9: s = self.norm(m3, s)
            out.append(s)
        seen = set(); res = []
        for s in out:
            key = tuple(sorted((J, round(v, 6)) for J, v in s.items() if v > 1e-9))
            if key not in seen: seen.add(key); res.append(s)
        return res

    def line_cands(self, m3):
        """LP-guided requests: for every reading among replies 1..3 and every future line f, the optimal line f
        (as masses on the current types, split proportionally inside a projected type), cut or padded to mass t"""
        out = []
        for rd in self.readings:
            if max(rd.R) >= 3: continue
            mu = self.proj(m3, rd.R)
            if rd.need(mu) >= INF: continue
            x = list(rd.h.getSolution().col_value)
            for e in range(len(rd.F)):
                lm = [0.0] * (1 << rd.r)
                for ci, (hh, E) in enumerate(rd.cols):
                    if e in E: lm[hh] += x[ci]
                s = {}
                for J, v in m3.items():
                    hh = 0
                    for i, xx in enumerate(rd.R):
                        if J >> xx & 1: hh |= 1 << i
                    if mu[hh] > 1e-12: s[J] = v * min(1.0, lm[hh] / mu[hh])
                out.append(self.norm(m3, s))
        return out

    def best4(self, m3, vprev, rng, iters=150, log=None):
        """her best stage-4 request against his menu: structured + LP-guided starts, then compass search"""
        order = {}
        cands = self.line_cands(m3) + self.cand4(m3)[:200]
        scored = []
        best, bs = vprev, None
        for s in cands:
            v, _ = self.value4(m3, s, vprev, order=order)
            scored.append((v, len(scored), s))
            if v < best - 1e-9: best, bs = v, s
        scored.sort()
        types = sorted(m3)
        starts = [s for _, _, s in scored[:4]] + [self.norm(m3, {J: rng.random() * m3[J] for J in m3}) for _ in range(3)]
        for s0 in starts:
            cur = dict(s0); cv, _ = self.value4(m3, cur, vprev, order=order)
            for delta in (0.06, 0.03, 0.015, 0.007, 0.003):
                improved = True; sweeps = 0
                while improved and sweeps < iters:
                    improved = False; sweeps += 1
                    for a in types:
                        for b in types:
                            if a == b: continue
                            x = min(delta, cur.get(a, 0.0), m3[b] - cur.get(b, 0.0))
                            if x <= 1e-9: continue
                            s = dict(cur); s[a] = s.get(a, 0.0) - x; s[b] = s.get(b, 0.0) + x
                            v, _ = self.value4(m3, s, vprev, incumbent=cv, order=order)
                            if v < cv - 1e-9: cur, cv = s, v; improved = True
            if cv < best - 1e-9: best, bs = cv, cur
        if bs is None: return best, None
        v, wd = self.value4(m3, bs, vprev, rich=True)
        return v, bs


def nm5(J): return "".join(str(i + 1) for i in range(5) if J >> i & 1) or "-"
def nm(J): return "".join(str(i + 1) for i in range(4) if J >> i & 1) or "-"
def fmt(d): return {nm(J): round(v, 4) for J, v in sorted(d.items()) if v > 1e-6}


def s3_candidates(G, m2, rng, extra=6):
    t, om = G.t, G.om; o = m2[3]; g = m2.get(0, 0.0); out = []
    for sO in (0.0, om / 2, om, min(o, 2 * om), o):
        for sg in sorted({min(g, x) for x in (g, max(0.0, g - om), g / 2, t - 2 * (G.N / 2 - 0.625) - sO)} ):
            if sg < 0: continue
            rest = t - sO - sg
            if rest < 0 or rest / 2 > m2[1] + 1e-12: continue
            out.append({3: sO, 1: rest / 2, 2: rest / 2, 0: sg})
            if rest / 2 + om / 2 <= m2[1]: out.append({3: sO, 1: rest / 2 + om / 2, 2: rest / 2 - om / 2, 0: sg})
    a = G.N / 2 - 0.625
    for j in range(-2, 7):
        x = a - j * om / 8
        if 0 <= x <= m2[1] and 0 <= t - 2 * x <= g: out.append({3: 0.0, 1: x, 2: x, 0: t - 2 * x})
    for _ in range(extra):
        s = G.norm(m2, {J: rng.random() * m2[J] for J in m2}); out.append(s)
    seen = set(); res = []
    for s in out:
        if abs(sum(s.values()) - t) > 1e-9 or any(v < -1e-12 or v > m2[J] + 1e-12 for J, v in s.items()): continue
        key = tuple(sorted((J, round(v, 6)) for J, v in s.items()))
        if key not in seen: seen.add(key); res.append(s)
    return res


def run(t, N, o, seed=0, iters=150, out=None):
    G = Game(t, N); rng = random.Random(seed); c = N - 1
    m2 = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}
    m2 = {J: v for J, v in m2.items() if v > 1e-12}
    v2, _ = G.need(m2, nrep=2)
    def W(d):
        if out: out.write(json.dumps(d) + "\n"); out.flush()
        print(json.dumps(d), flush=True)
    W(dict(start=True, t=t, N=N, o=o, omega=G.om, base=G.base, need_pair=v2))
    bestS = None; bestV = INF; t0 = time.time()
    for s3 in s3_candidates(G, m2, rng):
        worst = -INF; wrow = None
        for d3 in G.dump_menu(m2, s3):
            m3 = G.step(m2, s3, d3, 4)
            vprev, _ = G.need(m3, nrep=3)
            if vprev <= worst + 1e-9: continue                     # this dump cannot be his best
            v4, s4 = G.best4(m3, vprev, rng, iters)
            if v4 > worst: worst, wrow = v4, dict(d3=fmt(d3), need_after3=vprev, need_after4=v4, s4=fmt(s4) if s4 else None)
            if worst >= bestV - 1e-9: break                        # s3 cannot beat her incumbent
        W(dict(s3=fmt(s3), value=worst, his_best=wrow, pruned=worst >= bestV - 1e-9 and bestS is not None, secs=round(time.time() - t0), lps=G.nlp))
        if worst < bestV: bestV, bestS = worst, s3
    W(dict(SUMMARY=True, t=t, N=N, o=o, omega=G.om, base=G.base, need_pair=v2, value=bestV, saving_in_omega=(G.base - bestV) / G.om,
           cost_in_omega=2 - (G.base - bestV) / G.om, s3=fmt(bestS), secs=round(time.time() - t0), lps=G.nlp))


if __name__ == "__main__":
    t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    iters = int(sys.argv[5]) if len(sys.argv) > 5 else 150
    run(t, N, o, seed, iters, open(f"logs/twostage_t{t}_N{N}_o{o}_s{seed}.log", "w") if len(sys.argv) > 6 else None)
