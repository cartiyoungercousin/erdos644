"""CORE Part IX: her local search for a request with NO spoiling dump (objective: number of menu spoilers).
Positions from self-play (random request among those he spoils, random spoiler).  A request with 0 menu spoilers is
re-examined against a rich menu and random priority fills; survivors are written as CANDIDATE lines.
Usage: py spoil_hunt.py t N o seed depth iters [ncand]"""
import sys, json, random, time
import spoil as SP
INF = SP.INF

def spoilers(E, m, nrep, s, target, rich=1, cap=None):
    bit = 1 << nrep; sp = []
    for d in E.menu(m, s, rich):
        m2 = E.step(m, s, d, bit)
        v = E.min_need(m2, nrep + 1, new=nrep, stop_below=target)
        if v >= target - 1e-9:
            sp.append(d)
            if cap is not None and len(sp) > cap: break
    return sp

def random_fills(E, m, s, rng, n):
    free = {J: m[J] - s.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}
    types = list(free); out = []
    for _ in range(n):
        mode = rng.random()
        if mode < 0.5:
            od = types[:]; rng.shuffle(od)
            if rng.random() < 0.5: od.sort(key=lambda J: -SP.popc(J) + 2 * rng.random())
            d = {}; left = E.om; frac = rng.choice([1.0, 1.0, 0.5, 0.33])
            for J in od:
                x = min(free[J], left, E.om * frac) if frac < 1 else min(free[J], left)
                if x > 0: d[J] = x; left -= x
                if left <= 1e-12: break
            if left > 1e-12:
                for J in od:
                    x = min(free[J] - d.get(J, 0.0), left)
                    if x > 0: d[J] = d.get(J, 0.0) + x; left -= x
        else:
            w = {J: free[J] * rng.random() ** 3 for J in types}; tot = sum(w.values())
            d = {J: E.om * v / tot for J, v in w.items()}
            # clip
            for _ in range(30):
                ex = sum(max(0.0, d[J] - free[J]) for J in d)
                if ex < 1e-12: break
                room = {J: free[J] - d[J] for J in d if d[J] < free[J]}; R = sum(room.values())
                d = {J: min(d[J], free[J]) + (ex * room[J] / R if J in room else 0.0) for J in d}
        out.append(d)
    return out

def hunt(E, m, nrep, s0, target, rng, iters, W, tag):
    cur = dict(s0); sp = spoilers(E, m, nrep, cur, target); best = len(sp)
    types = sorted(m)
    for it in range(iters):
        if best == 0: break
        s = dict(cur)
        nmoves = rng.choice([1, 1, 2])
        for _ in range(nmoves):
            if sp and rng.random() < 0.6:
                d = rng.choice(sp); b = max(d, key=lambda J: d[J])
            else: b = rng.choice(types)
            room = m[b] - s.get(b, 0.0)
            if room <= 1e-9: continue
            donors = [a for a in types if a != b and s.get(a, 0.0) > 1e-9]
            if not donors: continue
            a = rng.choice(donors)
            delta = rng.choice([room, room, 0.08, 0.04, 0.02, 0.01])
            x = min(delta, room, s[a]); s[a] -= x; s[b] = s.get(b, 0.0) + x
        sp2 = spoilers(E, m, nrep, s, target, cap=best)
        if len(sp2) <= best:
            if len(sp2) < best: W(dict(tag=tag, it=it, spoilers=len(sp2)))
            cur, sp, best = s, sp2, len(sp2)
    if best == 0:
        sp_r = spoilers(E, m, nrep, cur, target, rich=2)
        nr = 0
        if not sp_r:
            bit = 1 << nrep; bestv = -INF
            for d in random_fills(E, m, cur, rng, 3000):
                v = E.min_need(E.step(m, cur, d, bit), nrep + 1, new=nrep, stop_below=target)
                if v >= target - 1e-9: nr += 1; break
                bestv = max(bestv, v)
        W(dict(CANDIDATE=(not sp_r and nr == 0), tag=tag, nrep=nrep, target=target, rich_spoilers=len(sp_r), random_spoiler=nr,
               pos={str(J): v for J, v in m.items()}, s={str(J): v for J, v in cur.items() if v > 1e-12}))
    return best, cur

if __name__ == "__main__":
    t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    seed, depth, iters = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    ncand = int(sys.argv[7]) if len(sys.argv) > 7 else 30
    E = SP.Engine(t, N); rng = random.Random(seed); c = N - 1
    f = open(f"logs/hunt_t{t}_N{N}_o{o}_s{seed}_d{depth}.log", "w")
    def W(d):
        f.write(json.dumps(d) + "\n"); f.flush(); print(json.dumps(d)[:300], flush=True)
    play = 0
    while True:
        m = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}; nrep = 2; play += 1
        while nrep < depth:
            t0 = time.time()
            cs, vold = E.cands(m, nrep, rng); rng.shuffle(cs); cs = cs[:ncand]
            target = min(vold, E.base); rows = []
            for s in cs:
                sp = spoilers(E, m, nrep, s, target)
                rows.append((len(sp), rng.random(), s, sp))
            rows.sort(key=lambda r: r[:2])
            res = []
            if nrep >= 3:
                for k, _, s, sp in rows[:3]:
                    b, sb = hunt(E, m, nrep, s, target, rng, iters, W, f"s{seed}p{play}n{nrep}")
                    res.append((k, b))
            W(dict(tag=f"s{seed}p{play}", nrep=nrep, ncells=len(m), vold=vold, start_to_final=res, secs=round(time.time() - t0), lps=E.nlp))
            ok = [r for r in rows if r[0] > 0]
            if not ok: break
            _, _, s, sp = rng.choice(ok); d = rng.choice(sp)
            m = E.step(m, s, d, 1 << nrep); nrep += 1
        if play >= 1000: break
