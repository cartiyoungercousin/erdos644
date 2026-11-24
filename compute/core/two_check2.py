"""finer outer dump search around the spoilers of a LEVEL2 candidate (CORE Part IX)"""
import sys, json, random, itertools
import spoil as SP, spoil_hunt as H, spoil_two as TW
fn, idx = sys.argv[1], int(sys.argv[2]); t, N = float(sys.argv[3]), float(sys.argv[4])
row = [json.loads(l) for l in open(fn) if "LEVEL2" in l][idx]
E = SP.Engine(t, N); rng = random.Random(7); nrep = row["nrep"]; target = row["target"]; om = E.om
m = {int(J): v for J, v in row["pos"].items()}; s = {int(J): v for J, v in row["s"].items()}
free = {J: m[J] - s.get(J, 0.0) for J in m}; free = {J: v for J, v in free.items() if v > 1e-9}
bit = 1 << nrep; cells = sorted(free)
core = [int(x) for x in sys.argv[5].split(",")]          # cells carrying the known spoilers
ds = []
for J in core:
    for K in cells:
        if K == J: continue
        for lam in (0.95, 0.9, 0.8, 0.7, 0.6, 0.5, 0.4, 0.25):
            a = min(free[J], lam * om); b = om - a
            if b <= free[K] + 1e-12: ds.append({J: a, K: b})
    for K, L in itertools.combinations([c for c in cells if c != J], 2):
        for lam in (0.8, 0.6):
            a = min(free[J], lam * om); b = (om - a) / 2
            if b <= free[K] and b <= free[L]: ds.append({J: a, K: b, L: b})
sp = [d for d in ds if E.min_need(E.step(m, s, d, bit), nrep + 1, new=nrep, stop_below=target) >= target - 1e-9]
print("fine outer dumps:", len(ds), "spoilers:", len(sp), flush=True)
rob = 0; rng.shuffle(sp)
for d in sp[:int(sys.argv[6])]:
    sb, tg = TW.break1(E, E.step(m, s, d, bit), nrep + 1, rng, 250, 30)
    print("  d", SP.fmt(d), "ROBUST" if sb is None else "broken", flush=True)
    if sb is None: rob += 1
print("robust:", rob)
