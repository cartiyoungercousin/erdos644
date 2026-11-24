import spoil as SP, spoil_hunt as H, random, json
E = SP.Engine(0.76, 1.9); rng = random.Random(0)
# position before the last request of the frozen line (6 replies), rebuilt from the log
rows = [json.loads(l) for l in open("logs/frozen_t0.76_N1.9_o0.33_s0.log")]
inv = lambda d: {sum(1 << (int(ch) - 1) for ch in k if ch != "-"): v for k, v in d.items()}
c = 0.9; o = 0.33; m = {3: o, 1: c - o, 2: c - o, 0: 1.9 - 2 * c + o}; nrep = 2
for r in rows[:-2]:
    m = E.step(m, inv(r["s"]), inv(r["d"]), 1 << nrep); nrep += 1
s = inv(rows[-2]["s"]); print("nrep", nrep, "pos", SP.fmt(m), "s", SP.fmt(s))
vold = E.min_need(m, nrep); print("vold", vold)
sp = H.spoilers(E, m, nrep, s, min(vold, E.base), rich=2)
print("unrestricted menu spoilers:", len(sp), [SP.fmt(d) for d in sp[:6]])
