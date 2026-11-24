"""CORE Part IX (60): re-check of the ROBUST spoiler found by p5_strong.py (index 80 of its dump list, seed 99).
Outer: confirm d80 spoils at the five-reply position.  Inner: repeated independent attempts (seed) of her break1 followed by
his climb; log every S2 and the best climbed value, and save the dumps reaching target.
Usage: py p5_verify.py seed idx tlimit_s   (idx = index into p5_strong's dump list)"""
import sys, json, random, time
import spoil as SP, spoil_hunt as H, spoil_two as TW, p5_strong as PS

def build_ds(E, m, s, om, nd=150):
    free = {J: m[J] - s.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}; cells = sorted(free)
    g = random.Random(99); ds = [{7: om}, {7: 0.105, 15: 0.035}, {7: 0.133, 31: 0.007}]
    while len(ds) < nd:
        lam = g.uniform(0.5, 1.0); a = lam * om; rest = om - a; d = {7: a}
        others = g.sample([c for c in cells if c != 7], g.choice([1, 1, 2, 3]))
        for i, K in enumerate(others):
            x = min(free[K], rest / (len(others) - i)); d[K] = x; rest -= x
        if rest < 1e-12: ds.append(d)
    return ds

if __name__ == "__main__":
    seed, idx, tl = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    row = json.loads(open("positions/p5_level2.json").readline())
    E = SP.Engine(0.76, 1.9); nrep = row["nrep"]; target = row["target"]; om = E.om; bit = 1 << nrep
    m = {int(J): v for J, v in row["pos"].items()}; s = {int(J): v for J, v in row["s"].items()}
    d = build_ds(E, m, s, om, idx + 1)[idx]
    v0 = E.min_need(E.step(m, s, d, bit), nrep + 1, new=nrep)
    m2 = E.step(m, s, d, bit)
    out = open(f"logs/p5_verify_{idx}_{seed}.log", "w")
    out.write(json.dumps(dict(d={str(J): x for J, x in d.items()}, outer_min_need=v0, target=target, base=E.base)) + "\n"); out.flush()
    rng = random.Random(seed); t0 = time.time()
    while time.time() - t0 < tl:
        sb, tg = TW.break1(E, m2, nrep + 1, random.Random(rng.random()), 300, 30)
        if sb is None: out.write(json.dumps(dict(S2=None)) + "\n"); out.flush(); continue
        v, dd = PS.climb(E, m2, nrep + 1, sb, tg, rng)
        out.write(json.dumps(dict(S2={str(J): x for J, x in sb.items() if x > 1e-12}, climbed=v, target=tg,
                                  answered=dd is not None, D2={str(J): x for J, x in (dd or {}).items() if x > 1e-12}, secs=round(time.time() - t0))) + "\n"); out.flush()
