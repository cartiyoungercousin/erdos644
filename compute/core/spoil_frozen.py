"""CORE Part IX: the stationary adversary suggested in CORE 38 -- the anti-plan rule FROZEN to the four cells of the
first pair (O = K1&K2, A, B, g): the dump goes to O as long as O has unrequested mass, then to A u B, then to g
(profile of D on the four cells = a fixed function of the profile of S); WHICH points inside a cell is his choice
(menu of priority fills over the sub-cells created by the play).  Her side: greedy descent, at each reply the request
minimising  max over his menu of the least need over all readings  (candidates + random local search).
Output: the need trajectory.  need <= 0 = she wins against this rule (against the menu: heuristic on his side).
Usage: py spoil_frozen.py t N o seed depth iters"""
import sys, json, random, itertools, time
import spoil as SP
INF = SP.INF

def menu(E, m, s, rng, nrand=6):
    free = {J: m[J] - s.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}
    stages = [[J for J in free if J & 3 == 3], [J for J in free if J & 3 in (1, 2)], [J for J in free if J & 3 == 0]]
    base = {}; left = E.om; part = None
    for st in stages:
        cap = sum(free[J] for J in st)
        if cap <= left + 1e-12:
            for J in st: base[J] = free[J]
            left -= cap
        else: part = st; break
        if left <= 1e-12: break
    if part is None or left <= 1e-12: return [base]
    out = []
    def fill(order, amounts=None):
        d = dict(base); l = left
        if amounts:
            for J, a in amounts:
                x = min(a, free[J], l); d[J] = d.get(J, 0.0) + x; l -= x
        for J in order:
            if l <= 1e-12: break
            x = min(free[J] - d.get(J, 0.0), l)
            if x > 0: d[J] = d.get(J, 0.0) + x; l -= x
        return d
    hi = sorted(part, key=lambda K: -SP.popc(K)); lo = hi[::-1]
    for J in part:
        out.append(fill([J] + [K for K in hi if K != J])); out.append(fill([J] + [K for K in lo if K != J]))
    for J, K in itertools.combinations(hi[:8], 2):
        out.append(fill([J, K] + hi, [(J, left / 2), (K, left / 2)]))
    tot = sum(free[J] for J in part); d = dict(base)
    for J in part: d[J] = left * free[J] / tot
    out.append(d)
    for _ in range(nrand):
        od = part[:]; rng.shuffle(od); out.append(fill(od))
    seen = set(); res = []
    for d in out:
        key = tuple(sorted((J, round(v, 9)) for J, v in d.items() if v > 1e-12))
        if key not in seen: seen.add(key); res.append(d)
    return res

def value(E, m, nrep, s, vold, rng, incumbent=None):
    bit = 1 << nrep; worst = -INF; wd = None
    for d in menu(E, m, s, rng):
        v = min(vold, E.min_need(E.step(m, s, d, bit), nrep + 1, new=nrep, stop_below=worst if worst > -INF else None))
        if v > worst: worst, wd = v, d
        if incumbent is not None and worst >= incumbent - 1e-9: break
    return worst, wd

if __name__ == "__main__":
    t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]); seed, depth, iters = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    E = SP.Engine(t, N); rng = random.Random(seed); c = N - 1
    f = open(f"logs/frozen_t{t}_N{N}_o{o}_s{seed}.log", "w")
    def W(d):
        f.write(json.dumps(d) + "\n"); f.flush(); print(json.dumps(d)[:700], flush=True)
    m = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}; nrep = 2
    while nrep < depth:
        t0 = time.time(); cs, vold = E.cands(m, nrep, rng, nline=60, nrand=15)
        best, bs, bd = INF, None, None
        for s in cs:
            v, d = value(E, m, nrep, s, vold, rng, incumbent=best if bs else None)
            if v < best - 1e-9: best, bs, bd = v, s, d
        types = sorted(m)
        for it in range(iters):
            s = dict(bs); a = rng.choice([J for J in types if s.get(J, 0.0) > 1e-9]); b = rng.choice(types)
            if a == b: continue
            room = m[b] - s.get(b, 0.0)
            x = min(rng.choice([room, s[a], 0.08, 0.04, 0.02, 0.01, 0.005]), room, s[a])
            if x <= 1e-9: continue
            s[a] -= x; s[b] = s.get(b, 0.0) + x
            v, d = value(E, m, nrep, s, vold, rng, incumbent=best)
            if v < best - 1e-9: best, bs, bd = v, s, d
        W(dict(nrep=nrep, ncells=len(m), need_before=vold, need_after=best, base=E.base, s=SP.fmt(bs), d=SP.fmt(bd), secs=round(time.time() - t0)))
        m = E.step(m, bs, bd, 1 << nrep); nrep += 1
        if best <= 1e-9: W(dict(HER_WIN=True, replies=nrep, pos=SP.fmt(m))); break
