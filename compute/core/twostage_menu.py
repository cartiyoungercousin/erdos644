"""Which reply-4 dumps does he need?  Same search as twostage.py with his reply-4 menu restricted:
mode 'prop' = proportional only; 'single' = one-type dumps only; 'high' = one-type dumps on types of co-degree >= 2 only.
Reply 3 keeps the full menu.  Usage: py twostage_menu.py t N o mode"""
import twostage as T, random, sys, json
mode = sys.argv[4]
class P(T.Game):
    def dump_menu(self, m, s, rich=False):
        full = T.Game.dump_menu(self, m, s, False)
        if len(m) <= 4: return full                      # reply 3
        nt = len([J for J in m if m[J] - s.get(J, 0.0) > 1e-9])
        if mode == "prop": return full[:1]
        if mode == "single": return full[1:1 + nt]
        if mode == "high":
            return [d for d in full[1:1 + nt] if bin(max(d, key=d.get)).count("1") >= 2] or full[:1]
t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
G = P(t, N); c = N - 1; rng = random.Random(0)
m2 = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}
bestV = T.INF; rows = []
for s3 in T.s3_candidates(G, m2, rng):
    worst = -T.INF; w = None
    for d3 in G.dump_menu(m2, s3):
        m3 = G.step(m2, s3, d3, 4); vprev, _ = G.need(m3, nrep=3)
        if vprev <= worst + 1e-9: continue
        v4, s4 = G.best4(m3, vprev, rng, 6)
        if v4 > worst: worst, w = v4, (T.fmt(d3), T.fmt(s4) if s4 else None, T.fmt(m3))
        if worst >= bestV - 1e-9: break
    if worst < bestV: bestV = worst; print(json.dumps(dict(value=worst, s3=T.fmt(s3), his_d3=w[0], s4=w[1], state3=w[2])), flush=True)
print(json.dumps(dict(SUMMARY=True, mode=mode, t=t, N=N, o=o, base=G.base, value=bestV, cost_in_omega=2 - (G.base - bestV) / G.om)))
