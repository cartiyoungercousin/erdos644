"""CORE Part VII: the exploration game one step deeper (three extra replies K3, K3', K4; five replies in all).

Model (see CORE 29): all replies are kept, she may use any of them, he answers every request once and sees everything
asked so far.  This IS the family statement (CP) truncated to three exploration steps; "consistency" adds nothing to it.
    value = min_{S3} max_{D3} min_{S3'} max_{D3'} min_{S4} max_{D4}  min over readings R (2..5 of the 5 replies) of need_R.
What is computed here, for ONE reply-3 request (the triangle-type one) and his reply-3 dumps in a given order:
  - her second request S3' ranges over a finite candidate list (heuristic level);
  - for each, his reply D3' ranges over the piecewise-linear menu of twostage_cert (all on one type; one type then a
    partner; proportional);
  - her last request S4 (over 16 types) is searched heuristically (best_last: candidate lines of every reading, then
    compass search) against his numeric priority-fill menu (fill_menu).  The exact MILP version (last_level) is kept
    but NOT used: against the piecewise-linear menu she parks the free mass of the high cells exactly at omega, where
    a two-type fill stops being available; that menu is too weak there (CORE 30).
Output per (S3, D3): for every candidate S3' the best he can do, max over D3' of min(need before reply 5, need after it).
Usage: py deep.py t N o [milp_seconds] [max candidates]
"""
import sys, json, time, random, itertools
import pulp
import twostage as T
import twostage_cert as C

NREP = 5; DEBUG = False


class Game5(T.Game):
    def __init__(self, t, N, pen=C.PEN):
        self.t, self.N = t, N; self.c = N - 1; self.om = N - 1 - t; self.base = self.om - 4 * (t - 0.75)
        self.readings = []
        for r in (2, 3, 4, 5):
            for R in itertools.combinations(range(NREP), r):
                for phi in T.patterns(r): self.readings.append(T.Reading(R, phi, t, self.om, pen))
        self.nlp = 0

    def needs(self, m, nrep, new=None):
        """min need over readings among the first nrep replies; new: only readings containing reply index `new`"""
        best = T.INF
        for rd in self.readings:
            if max(rd.R) >= nrep: continue
            if new is not None and new not in rd.R: continue
            v = rd.need(self.proj(m, rd.R))
            if v < best: best = v
        return best

    def cands(self, m, nrep, rng, k=14):
        """her candidate requests at a position with nrep replies: LP-optimal future lines of every reading, plus
        requests avoiding all points of co-degree >= 2, plus unions of whole types by co-degree"""
        out = []
        for rd in self.readings:
            if max(rd.R) >= nrep or len(rd.R) < 2: continue
            mu = self.proj(m, rd.R)
            if rd.need(mu) >= T.INF: continue
            x = list(rd.h.getSolution().col_value)
            for e in range(len(rd.F)):
                lm = [0.0] * (1 << rd.r)
                for ci, (hh, E) in enumerate(rd.cols):
                    if e in E: lm[hh] += x[ci]
                s = {}
                for J, v in m.items():
                    hh = 0
                    for i, xx in enumerate(rd.R):
                        if J >> xx & 1: hh |= 1 << i
                    if mu[hh] > 1e-12: s[J] = v * min(1.0, lm[hh] / mu[hh])
                out.append(self.norm(m, s))
        for order in (lambda J: (C.popc(J), J), lambda J: (-C.popc(J), J), lambda J: (C.popc(J), -J)):
            s = {}; left = self.t
            for J in sorted(m, key=order):
                x = min(m[J], left); s[J] = x; left -= x
            out.append(s)
        seen = set(); res = []
        for s in out:
            key = tuple(sorted((J, round(v, 3)) for J, v in s.items() if v > 1e-3))
            if key not in seen and abs(sum(s.values()) - self.t) < 1e-9: seen.add(key); res.append(s)
        rng.shuffle(res)
        return res[:k]


def last_level(G, m, new, tl=120, maxit=5, seeds=250, rng=None):
    """exact (MILP + LP-dual cuts) lower bound of  min_S max_{D in menu} min_{R containing reply `new`} need_R  at position m"""
    t, om = G.t, G.om; rng = rng or random.Random(0)
    m = {J: v for J, v in m.items() if v > 1e-9}; types = sorted(m); menu = C.menu(types)
    rds = [(i, rd) for i, rd in enumerate(G.readings) if max(rd.R) <= new and new in rd.R]
    cuts = {i: set() for i, _ in rds}
    bit = 1 << new
    def numeric_dump(e, free):
        return {J: max(0.0, x) for J, x in C.dump_of(e, free, om).items()}
    def available(e, free):
        if e[0] == "prop": return True
        if e[-1] == "a": return free[e[0]] >= om - 1e-9
        return free[e[0]] <= om + 1e-9 and free[e[0]] + free[e[1]] >= om - 1e-9
    def evaluate(S):
        """true value at S against the menu (closed availability), adding cuts"""
        free = {J: m[J] - S.get(J, 0.0) for J in m}; worst = -1.0; added = 0
        for e in menu:
            if not available(e, free): continue
            m2 = G.step(m, S, numeric_dump(e, free), bit); ve = T.INF
            for i, rd in rds:
                x, a, cc = C.lp_dual(rd, G.proj(m2, rd.R), t, om); ve = min(ve, x)
                if (a, cc) not in cuts[i]: cuts[i].add((a, cc)); added += 1
            worst = max(worst, ve)
        return worst, added
    best_true = T.INF
    for _ in range(seeds):
        S = G.norm(m, {J: (rng.random() ** 2) * m[J] * (rng.random() < 0.6) for J in m})
        v, _ = evaluate(S); best_true = min(best_true, v)
    lb = -1.0; S = None
    for it in range(maxit):
        prob = pulp.LpProblem("last", pulp.LpMinimize); cnt = [0]
        def V(lo=0.0, hi=None, cat="Continuous"):
            cnt[0] += 1; return prob.add_variable(f"x{cnt[0]}", lo, hi, cat)
        def Cn(con): prob.__iadd__(con)
        v = V(0.0, 3.0); prob += v
        s = {J: V(0.0, m[J]) for J in m}; Cn(pulp.lpSum(s.values()) == t)
        free = {J: m[J] - s[J] for J in m}; AV = {}; dbg = []
        for e in menu:
            a = None
            if e[0] != "prop":
                a = V(cat="Binary")
                if e[-1] == "a":
                    J = e[0]; AV[J] = a
                    Cn(free[J] >= om - C.MA * (1 - a)); Cn(free[J] <= om + C.MA * a)
                else:
                    J, J2 = e[0], e[1]; f = V(cat="Binary")
                    Cn(free[J] <= om + C.MA * (1 - a)); Cn(free[J] + free[J2] >= om - C.MA * (1 - a))
                    Cn(free[J] >= om - C.MA * (a + f)); Cn(free[J] + free[J2] <= om + C.MA * (a + 1 - f))
                    Cn(AV[J] >= 1 - a - f)
            d = C.dump_of(e, free, om); m2 = {}
            for J in m:
                m2[J | bit] = s[J] + d[J]; m2[J] = m[J] - s[J] - d[J]
            zs = []
            for i, rd in rds:
                z = V(cat="Binary"); zs.append(z)
                mu = [0] * (1 << rd.r)
                for J, ex in m2.items():
                    hh = 0
                    for k, x in enumerate(rd.R):
                        if J >> x & 1: hh |= 1 << k
                    mu[hh] = mu[hh] + ex
                live = {h2 for (h2, E) in rd.cols}
                relax = 0 if a is None else C.BIGM * (1 - a)
                for hh in rd.hs:
                    if hh not in live:
                        if isinstance(mu[hh], (int, float)):
                            if mu[hh] > 1e-9: Cn(z <= 0)
                        else: Cn(mu[hh] <= C.MA * (1 - z) + (0 if a is None else C.MA * (1 - a)))
                for (al, cc) in cuts[i]:
                    Cn(pulp.lpSum(al[hh] * mu[hh] for hh in rd.hs if al[hh] != 0.0) + cc <= v + C.BIGM * (1 - z) + relax)
            Cn(pulp.lpSum(zs) >= 1); dbg.append((e, a, zs, m2))
        res = prob.solve(pulp.HiGHS(msg=False, timeLimit=tl))
        vm = pulp.value(v)
        try: lb = prob.solverModel.getInfo().mip_dual_bound
        except Exception: lb = vm if res.status_str == "Optimal" else lb
        if vm is None: break
        S = {J: min(max(0.0, pulp.value(x) or 0.0), m[J]) for J, x in s.items()}
        tv, added = evaluate(S); best_true = min(best_true, tv)
        if DEBUG and tv > vm + 1e-4 and added == 0:
            pv = lambda x: x if isinstance(x, (int, float)) else (pulp.value(x) or 0.0)
            fr = {J: m[J] - S[J] for J in m}
            for (e, a, zs, m2s) in dbg:
                av = available(e, fr); am = None if a is None else pv(a)
                mnum = G.step(m, S, numeric_dump(e, fr), bit) if av else None
                row = []
                for (i, rd), z in zip(rds, zs):
                    if pv(z) > 0.5:
                        mus = [0.0] * (1 << rd.r)
                        for J, ex in m2s.items():
                            hh = 0
                            for k, x in enumerate(rd.R):
                                if J >> x & 1: hh |= 1 << k
                            mus[hh] += pv(ex)
                        cm = max(sum(al[hh] * mus[hh] for hh in rd.hs) + cc for (al, cc) in cuts[i])
                        row.append((rd.R, rd.phi, round(cm, 4), round(rd.need(mus), 4), None if mnum is None else round(rd.need(G.proj(mnum, rd.R)), 4), [round(x, 4) for x in mus]))
                tve = None if mnum is None else min(rd.need(G.proj(mnum, rd.R)) for i, rd in rds)
                if tve is not None and tve > vm + 1e-4: print("DBG", e, "avail true", av, "milp a", am, "true min need", round(tve, 4), "free", {T.nm5(J): round(x, 4) for J, x in fr.items() if J in e[:-1] or e[0] == "prop"}, row[:2], flush=True)

        if lb >= G.base - 1e-6 or added == 0 or (res.status_str == "Optimal" and tv <= vm + 1e-6): break
    return lb, best_true, S


def fill_menu(G, m, S, rich=True):
    """his numeric menu at a position: proportional; all on J with spill to the other types by descending co-degree;
    half-half on two types of co-degree >= 2 (then spill).  Every dump has mass exactly N - 1 - |S|."""
    free = {J: m[J] - S.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}
    om = G.N - 1 - sum(S.values()); types = sorted(free); tot = sum(free.values()); out = [{J: om * v / tot for J, v in free.items()}]
    by_hi = sorted(types, key=lambda K: (-C.popc(K), K))
    def fill(first, amounts=None):
        d = {}; left = om
        for J, a in (amounts or []):
            x = min(a, free[J], left); d[J] = d.get(J, 0.0) + x; left -= x
        for J in first + [K for K in by_hi if K not in first]:
            if left <= 1e-12: break
            x = min(free[J] - d.get(J, 0.0), left)
            if x > 0: d[J] = d.get(J, 0.0) + x; left -= x
        return d
    for J in types: out.append(fill([J]))
    if rich:
        hi = [J for J in types if C.popc(J) >= 2]
        for J, K in itertools.combinations(hi, 2): out.append(fill([J, K], [(J, om / 2), (K, om / 2)]))
        for J in types: out.append(fill([J] + sorted([K for K in types if K != J], key=lambda K: (C.popc(K), K))))
    return out


def value_last(G, m, S, new, cap, order, incumbent=None):
    """max over his menu of min over readings through the new reply (pairs excluded: they never beat base), capped"""
    bit = 1 << new; worst = -T.INF; wk = None
    menu = fill_menu(G, m, S)
    idx = sorted(range(len(menu)), key=lambda i: -order.get(i, 0))
    for i in idx:
        m2 = G.step(m, S, menu[i], bit); v = cap
        for rd in G.readings:
            if max(rd.R) > new or new not in rd.R or len(rd.R) < 3: continue
            x = rd.need(G.proj(m2, rd.R))
            if x < v: v = x
            if v < worst - 1e-9: break
        if v > worst: worst, wk = v, i
        if incumbent is not None and worst >= incumbent - 1e-9: break
    if wk is not None: order[wk] = order.get(wk, 0) + 1
    return worst


def best_last(G, m, new, cap, rng, kc=60):
    """her best last request (heuristic): candidates, then compass search from the two best"""
    m = {J: v for J, v in m.items() if v > 1e-9}; order = {}; scored = []
    for S in G.cands(m, new, rng, kc):
        S = {J: v for J, v in S.items() if J in m}
        scored.append((value_last(G, m, S, new, cap, order), len(scored), S))
    scored.sort(); best, bs = scored[0][0], scored[0][2]
    types = sorted(m)
    for _, _, s0 in scored[:2]:
        cur = dict(s0); cv = value_last(G, m, cur, new, cap, order)
        for delta in (0.05, 0.02, 0.008):
            improved = True; sweeps = 0
            while improved and sweeps < 4:
                improved = False; sweeps += 1
                for a in types:
                    for b in types:
                        if a == b: continue
                        x = min(delta, cur.get(a, 0.0), m[b] - cur.get(b, 0.0))
                        if x <= 1e-9: continue
                        s = dict(cur); s[a] = s.get(a, 0.0) - x; s[b] = s.get(b, 0.0) + x
                        v = value_last(G, m, s, new, cap, order, incumbent=cv)
                        if v < cv - 1e-9: cur, cv = s, v; improved = True
        if cv < best - 1e-9: best, bs = cv, cur
    return best, bs


def main(t, N, o, tl=120, kc=14):
    G = Game5(t, N); c = N - 1; om = G.om; rng = random.Random(0); a = N / 2 - 0.625
    m2 = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}
    log = open(f"logs/deep_t{t}_N{N}_o{o}.log", "w")
    def W(d): log.write(json.dumps(d) + "\n"); log.flush(); print(json.dumps(d)[:500], flush=True)
    W(dict(start=True, t=t, N=N, o=o, omega=om, base=G.base, readings=len(G.readings)))
    S3 = {3: 0.0, 1: a, 2: a, 0: t - 2 * a}
    t0 = time.time(); top = []
    for name, d3 in (("all of omega on O (pile)", {3: om}), ("proportional", {J: (om / (1 + om)) * (m2[J] - S3[J]) for J in m2})):
        m3 = G.step(m2, S3, d3, 4); v3 = G.needs(m3, 3)
        her_best = T.INF; rows = []
        for S3b in G.cands(m3, 3, rng, kc):
            free = {J: m3[J] - S3b.get(J, 0.0) for J in m3}
            opts = []
            for e in C.menu(sorted(m3)):
                if e[0] != "prop":
                    if e[-1] == "a" and free[e[0]] < om - 1e-9: continue
                    if e[-1] == "b" and not (free[e[0]] <= om + 1e-9 and free[e[0]] + free[e[1]] >= om - 1e-9): continue
                d = {J: max(0.0, x) for J, x in C.dump_of(e, free, om).items()}
                m4 = G.step(m3, S3b, d, 8); v4 = G.needs(m4, 4)
                opts.append((v4, -C.popc(e[0]) if e[0] != "prop" else 0, str(e), m4))
            opts.sort(key=lambda r: (-r[0], r[1]))
            his = -1.0; hrow = None
            for (v4, _, ename, m4) in opts[:4]:
                if v4 <= his + 1e-9: break
                v5, S4 = best_last(G, m4, 4, v4, rng)
                val_lb = min(v4, v5)
                if val_lb > his: his, hrow = val_lb, dict(d3b=ename, need_after4=v4, need_after5=v5, s4=None if S4 is None else {T.nm5(J): round(x, 4) for J, x in S4.items() if x > 1e-4}, state4={T.nm5(J): round(x, 4) for J, x in m4.items() if x > 1e-4})
                if his >= G.base - 1e-6: break
            rows.append(dict(s3b=T.fmt(S3b), his_value_lb=his, his=hrow))
            her_best = min(her_best, his)
            W(dict(d3=name, s3b=T.fmt(S3b), his_value_lower_bound=his, his=hrow, secs=round(time.time() - t0)))
        W(dict(D3=name, need_after3=v3, her_best_over_candidates=her_best, in_omega=2 - (G.base - min(her_best, G.base)) / om if her_best < T.INF else None,
               candidates=len(rows), secs=round(time.time() - t0)))
        top.append(her_best)
        if her_best >= G.base - 1e-6: break            # he has a reply-3 dump that holds: done for this S3
    W(dict(SUMMARY=True, t=t, N=N, o=o, omega=om, base=G.base, value_found=max(top), holds=max(top) >= G.base - 1e-6, secs=round(time.time() - t0)))


if __name__ == "__main__":
    a = sys.argv
    main(float(a[1]), float(a[2]), float(a[3]), float(a[4]) if len(a) > 4 else 120, int(a[5]) if len(a) > 5 else 14)
