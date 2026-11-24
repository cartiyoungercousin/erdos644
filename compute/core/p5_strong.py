"""CORE Part IX (60): attack on the five-reply candidate with a stronger adversary (hill-climbing dumps at the inner level).
For outer spoilers d (known region: most of the dump on cell 123, plus random ones) find her second request S2
(break1) and then let HIM climb: maximise over D2 the least need over readings containing the last reply.
A spoiler d for which every S2 found is answered by a climbed spoiling D2 is ROBUST -> the candidate is dead.
Usage: py p5_strong.py part nparts ndumps"""
import sys, json, random
import spoil as SP, spoil_hunt as H, spoil_two as TW
INF = SP.INF

def climb(E, m, nrep, s, target, rng, starts=6, moves=150):
    bit = 1 << nrep
    free = {J: m[J] - s.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}; cells = list(free)
    f = lambda d, lb=None: E.min_need(E.step(m, s, d, bit), nrep + 1, new=nrep, stop_below=lb)
    pool = []
    for d in E.menu(m, s, 1) + H.random_fills(E, m, s, rng, 300):
        lb = pool[-1][0] if len(pool) >= starts else None
        v = f(d, lb)
        if lb is None or v > lb: pool.append((v, rng.random(), d)); pool.sort(key=lambda r: -r[0]); pool = pool[:starts]
    best = -INF
    for v, _, d in pool:
        v = f(d); d = dict(d)
        for _ in range(moves):
            if v >= target - 1e-9: return v, d
            a = rng.choice([J for J in d if d[J] > 1e-9]); b = rng.choice(cells)
            if a == b: continue
            x = min(rng.choice([d[a], d[a] / 2, d[a] / 4, 0.01, 0.003]), d[a], free[b] - d.get(b, 0.0))
            if x <= 1e-9: continue
            d2 = dict(d); d2[a] -= x; d2[b] = d2.get(b, 0.0) + x
            v2 = f(d2, v)
            if v2 > v + 1e-10: v, d = v2, d2
        best = max(best, v)
        if v >= target - 1e-9: return v, d
    return best, None

if __name__ == "__main__":
    part, nparts, nd = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    row = json.loads(open("positions/p5_level2.json").readline())
    E = SP.Engine(0.76, 1.9); nrep = row["nrep"]; target = row["target"]; om = E.om; bit = 1 << nrep
    m = {int(J): v for J, v in row["pos"].items()}; s = {int(J): v for J, v in row["s"].items()}
    free = {J: m[J] - s.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}; cells = sorted(free)
    g = random.Random(99); ds = [{7: om}, {7: 0.105, 15: 0.035}, {7: 0.133, 31: 0.007}]
    while len(ds) < nd:
        lam = g.uniform(0.5, 1.0); a = lam * om; rest = om - a; d = {7: a}
        others = g.sample([c for c in cells if c != 7], g.choice([1, 1, 2, 3]))
        for i, K in enumerate(others):
            x = min(free[K], rest / (len(others) - i)); d[K] = x; rest -= x
        if rest < 1e-12: ds.append(d)
    rng = random.Random(1000 + part); out = open(f"logs/p5_strong_{part}.log", "w")
    # his outer climb as well: any spoiler found by climbing from random starts joins the list (part 0 only)
    for i, d in enumerate(ds):
        if i % nparts != part: continue
        if E.min_need(E.step(m, s, d, bit), nrep + 1, new=nrep, stop_below=target) < target - 1e-9: continue
        m2 = E.step(m, s, d, bit); verdict = "ROBUST"; info = []
        for attempt in range(3):
            sb, tg = TW.break1(E, m2, nrep + 1, random.Random(rng.random()), 300, 30)
            if sb is None: info.append("no S2"); continue
            v, dd = climb(E, m2, nrep + 1, sb, tg, rng)
            if dd is None: verdict = "broken"; info.append(f"S2 holds against climb (his best {v:.5f} < {tg:.5f})"); break
            info.append("S2 answered by climbed dump")
        out.write(json.dumps(dict(i=i, d=SP.fmt(d), verdict=verdict, info=info)) + "\n"); out.flush()
