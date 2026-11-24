"""re-examine a LEVEL2 candidate with a rich outer dump search (CORE Part IX)"""
import sys, json, random
import spoil as SP, spoil_hunt as H, spoil_two as TW
fn, idx = sys.argv[1], int(sys.argv[2])
row = [json.loads(l) for l in open(fn) if "LEVEL2" in l][idx]
t, N = float(sys.argv[3]), float(sys.argv[4])
E = SP.Engine(t, N); rng = random.Random(5); nrep = row["nrep"]; target = row["target"]
m = {int(J): v for J, v in row["pos"].items()}; s = {int(J): v for J, v in row["s"].items()}
print("pos", SP.fmt(m)); print("s", SP.fmt(s))
bit = 1 << nrep; sp = []; seen = set()
for d in E.menu(m, s, 2) + H.random_fills(E, m, s, rng, 4000):
    key = tuple(sorted((J, round(v, 6)) for J, v in d.items() if v > 1e-9))
    if key in seen: continue
    seen.add(key)
    if E.min_need(E.step(m, s, d, bit), nrep + 1, new=nrep, stop_below=target) >= target - 1e-9: sp.append(d)
print("outer spoilers (rich + random):", len(sp), "of", len(seen), flush=True)
rob = 0
for d in sp[:40]:
    sb, tg = TW.break1(E, E.step(m, s, d, bit), nrep + 1, rng, 200, 30)
    print("  d", SP.fmt(d), "ROBUST" if sb is None else "broken", flush=True)
    if sb is None: rob += 1; break
print("robust spoiler found:", rob)
