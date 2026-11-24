"""CORE Part IX: one-level falsification test of SPOIL at positions with 4..6 kept replies (float LPs, HiGHS).

Position: masses of the co-type cells J (bitmask over the m kept replies).  One level:
    score(S) = max over his dumps D of  min over readings R containing the NEW reply of need_R,
SPOIL (base form) says score(S) >= base = omega - 4 eps for every request S.  A request with score < base against
his FULL dump polytope would break it; here his side is a menu (priority fills), so "score < base" is only a
CANDIDATE, to be re-examined with a richer dump search (spoil_his.py).
Readings: every subset R (2..7 replies) with every concurrency pattern (1, 2, 5, 15, 30, 30 patterns).
Usage: py spoil.py t N o seed nplays depth [ncand]
"""
import sys, json, time, random, itertools
import highspy
import twostage as T

INF = T.INF
popc = lambda x: bin(x).count("1")


class Pat:
    """a concurrency pattern of r replies, as an LP in the 2^r projected masses"""
    def __init__(self, r, phi, t, om):
        self.rd = T.Reading(tuple(range(r)), phi, t, om, None); self.r = r; self.phi = phi
        self.n = 1 << r
        self.idx = list(range(self.n))

    def need(self, mu):
        h = self.rd.h
        for hh in range(self.n): h.changeRowBounds(hh, mu[hh], mu[hh])
        h.run()
        if h.getModelStatus() != highspy.HighsModelStatus.kOptimal: return INF
        return h.getInfo().objective_function_value


class Engine:
    def __init__(self, t, N):
        self.t, self.N = t, N; self.c = N - 1; self.om = N - 1 - t; self.base = self.om - 4 * (t - 0.75)
        self.pats = {r: [Pat(r, phi, t, self.om) for phi in T.patterns(r)] for r in range(2, 8)}
        self.nlp = 0; self.hits = {}

    @staticmethod
    def proj(m, R):
        mu = [0.0] * (1 << len(R))
        for J, v in m.items():
            hh = 0
            for i, x in enumerate(R):
                if J >> x & 1: hh |= 1 << i
            mu[hh] += v
        return mu

    def readings(self, nrep, new=None):
        for r in range(2, min(7, nrep) + 1):
            for R in itertools.combinations(range(nrep), r):
                if new is not None and new not in R: continue
                for pi in range(len(self.pats[r])): yield (R, pi)

    def need_of(self, m, R, pi):
        self.nlp += 1
        return self.pats[len(R)][pi].need(self.proj(m, R))

    def min_need(self, m, nrep, new=None, stop_below=None, want_arg=False):
        keys = list(self.readings(nrep, new))
        keys.sort(key=lambda k: -self.hits.get(k, 0))
        best = INF; arg = None
        for (R, pi) in keys:
            v = self.need_of(m, R, pi)
            if v < best: best, arg = v, (R, pi)
            if stop_below is not None and best < stop_below - 1e-9:
                self.hits[arg] = self.hits.get(arg, 0) + 1; break
        return (best, arg) if want_arg else best

    step = staticmethod(T.Game.step)

    def norm(self, m, s, tgt=None):
        return T.Game.norm(self, m, s, tgt)

    # ---- his menu -------------------------------------------------------------------------------------------
    def menu(self, m, s, rich=1):
        free = {J: m[J] - s.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}
        om = self.om; types = sorted(free, key=lambda J: (-popc(J), -free[J]))
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
        hi = sorted(types, key=lambda K: -popc(K)); lo = sorted(types, key=lambda K: popc(K))
        for J in types:
            out.append(fill([J] + [K for K in hi if K != J]))
            if free[J] < om - 1e-9:
                out.append(fill([J] + [K for K in lo if K != J]))
                # spill into supersets / subsets of J first
                out.append(fill([J] + sorted([K for K in types if K != J], key=lambda K: (-popc(K & J), -popc(K)))))
        if rich >= 1:
            big = [J for J in types if popc(J) >= 2][:10]
            for J, K in itertools.combinations(big, 2):
                out.append(fill([J, K] + [L for L in hi if L not in (J, K)], [(J, om / 2), (K, om / 2)]))
        tot = sum(free.values()); out.append({J: om * v / tot for J, v in free.items()})
        if rich >= 2:
            for J, K in itertools.combinations(types, 2):
                out.append(fill([J, K] + [L for L in hi if L not in (J, K)], [(J, om / 2), (K, om / 2)]))
                out.append(fill([J, K] + [L for L in hi if L not in (J, K)], [(J, om / 4), (K, 3 * om / 4)]))
                out.append(fill([J, K] + [L for L in hi if L not in (J, K)], [(J, 3 * om / 4), (K, om / 4)]))
        seen = set(); res = []
        for d in out:
            key = tuple(sorted((J, round(v, 9)) for J, v in d.items() if v > 1e-12))
            if key not in seen: seen.add(key); res.append(d)
        return res

    def score(self, m, nrep, s, target, rich=1, all_spoilers=False):
        """max over the menu of min over new readings; stops at the first dump reaching target (a spoiler).
        returns (score, dump, list of spoilers if all_spoilers)"""
        bit = 1 << nrep; worst = -INF; wd = None; sp = []
        for d in self.menu(m, s, rich):
            m2 = self.step(m, s, d, bit)
            v = self.min_need(m2, nrep + 1, new=nrep, stop_below=max(worst, target) if not all_spoilers else target)
            if v > worst: worst, wd = v, d
            if v >= target - 1e-9:
                if not all_spoilers: return v, d, [d]
                sp.append(d)
        return worst, wd, sp

    # ---- her candidates -------------------------------------------------------------------------------------
    def cands(self, m, nrep, rng, nline=40, nrand=10):
        out = []
        # LP lines of the best readings
        rs = []
        for (R, pi) in self.readings(nrep):
            v = self.need_of(m, R, pi)
            if v < INF: rs.append((v, len(R), R, pi))
        rs.sort()
        vold = rs[0][0] if rs else INF
        pick = rs[:nline // 2] + rng.sample(rs, min(len(rs), nline // 2))
        for v, _, R, pi in pick:
            P = self.pats[len(R)][pi]; rd = P.rd
            mu = self.proj(m, R); P.need(mu)
            x = list(rd.h.getSolution().col_value)
            for e in range(len(rd.F)):
                lm = [0.0] * (1 << rd.r)
                for ci, (hh, E) in enumerate(rd.cols):
                    if e in E: lm[hh] += x[ci]
                # split inside a projected type: proportional / high co-degree first / low co-degree first
                for mode in (0, 1, 2):
                    s = {}
                    byh = {}
                    for J in m:
                        hh = 0
                        for i, xx in enumerate(R):
                            if J >> xx & 1: hh |= 1 << i
                        byh.setdefault(hh, []).append(J)
                    for hh, Js in byh.items():
                        want = min(lm[hh], mu[hh])
                        if want <= 1e-12: continue
                        if mode == 0:
                            for J in Js: s[J] = m[J] * want / mu[hh]
                        else:
                            for J in sorted(Js, key=lambda J: -popc(J) if mode == 1 else popc(J)):
                                x1 = min(m[J], want); s[J] = x1; want -= x1
                    s = self.fit(m, s, rng, mode)
                    out.append(s)
        types = sorted(m)
        for order in (lambda J: (popc(J), J), lambda J: (-popc(J), J), lambda J: (popc(J), -J), lambda J: (abs(popc(J) - 2), J)):
            s = {}; left = self.t
            for J in sorted(m, key=order):
                x = min(m[J], left); s[J] = x; left -= x
            out.append(s)
        for _ in range(nrand):
            od = types[:]; rng.shuffle(od); s = {}; left = self.t
            for J in od:
                x = min(m[J], left); s[J] = x; left -= x
            out.append(s)
            out.append(self.norm(m, {J: rng.random() * m[J] * (rng.random() < 0.6) for J in m}))
        seen = set(); res = []
        for s in out:
            key = tuple(sorted((J, round(v, 4)) for J, v in s.items() if v > 1e-4))
            if key not in seen and abs(sum(s.values()) - self.t) < 1e-9: seen.add(key); res.append(s)
        return res, vold

    def fit(self, m, s, rng, mode):
        """cut or pad a line to mass t: pad with low co-degree first (mode 0, 2) or high (1); cut proportionally"""
        tot = sum(s.values())
        if tot > self.t + 1e-12:
            f = self.t / tot; return {J: v * f for J, v in s.items()}
        left = self.t - tot
        for J in sorted(m, key=lambda J: (popc(J) if mode != 1 else -popc(J), rng.random())):
            if left <= 1e-12: break
            x = min(m[J] - s.get(J, 0.0), left)
            if x > 0: s[J] = s.get(J, 0.0) + x; left -= x
        return s


def nm(J): return "".join(str(i + 1) for i in range(8) if J >> i & 1) or "-"
def fmt(d): return {nm(J): round(v, 6) for J, v in sorted(d.items()) if v > 1e-9}


def play(E, m, nrep, depth, rng, ncand, W, tag):
    """self-play from position m: at each level test all candidate requests; continue along a random request"""
    while nrep < depth:
        t0 = time.time()
        cs, vold = E.cands(m, nrep, rng)
        rng.shuffle(cs); cs = cs[:ncand]
        target = min(vold, E.base)
        worst_for_him = INF; ws = None; rows = []
        for s in cs:
            v, d, _ = E.score(m, nrep, s, target)
            rows.append((v, s, d))
            if v < worst_for_him: worst_for_him, ws = v, s
            if v < target - 1e-7:
                v2, d2, _ = E.score(m, nrep, s, target, rich=2)
                W(dict(CANDIDATE=True, tag=tag, nrep=nrep, pos=fmt(m), s=fmt(s), menu_score=v, rich_score=v2, target=target, vold=vold))
        W(dict(tag=tag, nrep=nrep, ncells=len(m), vold=vold, base=E.base, ncand=len(cs), her_best=worst_for_him,
               holds=worst_for_him >= target - 1e-7, secs=round(time.time() - t0), lps=E.nlp, pos=fmt(m)))
        ok = [(v, s, d) for v, s, d in rows if v >= target - 1e-7]
        if not ok: return
        v, s, d = rng.choice(ok)
        m = E.step(m, s, d, 1 << nrep); nrep += 1


if __name__ == "__main__":
    t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    seed, nplays, depth = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    ncand = int(sys.argv[7]) if len(sys.argv) > 7 else 40
    E = Engine(t, N); rng = random.Random(seed); c = N - 1
    f = open(f"logs/spoil_t{t}_N{N}_o{o}_s{seed}_d{depth}.log", "w")
    def W(d):
        f.write(json.dumps(d) + "\n"); f.flush(); print(json.dumps(d)[:400], flush=True)
    for p in range(nplays):
        m2 = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}
        play(E, m2, 2, depth, rng, ncand, W, f"s{seed}p{p}")
