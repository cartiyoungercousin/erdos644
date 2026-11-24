"""Optimiser check: against the PROPORTIONAL dump at replies 3 and 4 (predictable) the exact-control lemma (CORE 13)
says she reaches need 0 after reply 4 (triangle K1 or K2 with K3, K4).  Does the search of twostage.py find it?"""
import twostage as T, random, sys
class P(T.Game):
    def dump_menu(self, m, s, rich=False): return T.Game.dump_menu(self, m, s)[:1]
t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
G = P(t, N); c = N - 1; rng = random.Random(0)
m2 = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}
def val(s3):
    m3 = G.step(m2, s3, G.dump_menu(m2, s3)[0], 4); vprev = G.need(m3, nrep=3)[0]
    v, s4 = G.best4(m3, vprev, rng, 6); return v, s4, vprev
best = None
for s3 in T.s3_candidates(G, m2, rng, extra=10):
    v, s4, vp = val(s3)
    if best is None or v < best[0]: best = (v, s3, s4, vp)
    print(round(v, 4), round(vp, 4), T.fmt(s3), flush=True)
cur, cv = best[1], best[0]
for delta in (0.04, 0.02, 0.01):
    imp = True
    while imp:
        imp = False
        for a in m2:
            for b in m2:
                if a == b: continue
                x = min(delta, cur.get(a, 0), m2[b] - cur.get(b, 0))
                if x <= 1e-9: continue
                s = dict(cur); s[a] = s.get(a, 0) - x; s[b] = s.get(b, 0) + x
                v, s4, vp = val(s)
                if v < cv - 1e-9: cur, cv, imp = s, v, True; best = (v, s, s4, vp); print("improved", round(v, 4), T.fmt(s), flush=True)
print("FINAL need", best[0], "after3", best[3], "s3", T.fmt(best[1]), "s4", T.fmt(best[2]) if best[2] else None, "base", G.base)
