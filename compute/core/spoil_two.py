"""CORE Part IX: two-level test along 'robust' play.
break1(pos): her search for a request with no spoiling dump (menu + rich menu + random fills)  -> request or None.
At a position, for each candidate request S: his menu spoilers d are tried (high co-degree first) until one is ROBUST
(break1 fails at the position after it).  If every spoiler of S is non-robust: LEVEL2 line (she breaks through in two
requests against the menu).  Play continues along a random (S, robust d).
Usage: py spoil_two.py t N o seed depth iters ncand [nS]"""
import sys, json, random, time
import spoil as SP, spoil_hunt as H
INF = SP.INF

def break1(E, m, nrep, rng, iters, ncand, starts=3):
    cs, vold = E.cands(m, nrep, rng); rng.shuffle(cs); cs = cs[:ncand]
    target = min(vold, E.base); rows = []
    for s in cs:
        sp = H.spoilers(E, m, nrep, s, target, cap=12)
        if not sp:
            got = confirm(E, m, nrep, s, target, rng)
            if got: return s, target
        rows.append((len(sp), rng.random(), s))
    rows.sort(key=lambda r: r[:2])
    for k, _, s in rows[:starts]:
        b, sb = H.hunt(E, m, nrep, s, target, rng, iters, lambda d: None, "")
        if b == 0 and confirm(E, m, nrep, sb, target, rng): return sb, target
    return None, target

def confirm(E, m, nrep, s, target, rng, n=1500):
    if H.spoilers(E, m, nrep, s, target, rich=2, cap=0): return False
    bit = 1 << nrep
    for d in H.random_fills(E, m, s, rng, n):
        if E.min_need(E.step(m, s, d, bit), nrep + 1, new=nrep, stop_below=target) >= target - 1e-9: return False
    return True

if __name__ == "__main__":
    t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    seed, depth, iters, ncand = int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    nS = int(sys.argv[8]) if len(sys.argv) > 8 else 12
    E = SP.Engine(t, N); rng = random.Random(seed); c = N - 1
    f = open(f"logs/two_t{t}_N{N}_o{o}_s{seed}_d{depth}.log", "w")
    def W(d):
        f.write(json.dumps(d) + "\n"); f.flush(); print(json.dumps(d)[:260], flush=True)
    play = 0
    while play < 500:
        m = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}; nrep = 2; play += 1
        while nrep < depth:
            t0 = time.time()
            cs, vold = E.cands(m, nrep, rng); rng.shuffle(cs); cs = cs[:nS]
            target = min(vold, E.base); cont = []; nlev2 = 0; nrob = 0
            for s in cs:
                sp = H.spoilers(E, m, nrep, s, target)
                if not sp:
                    W(dict(LEVEL1=True, tag=f"s{seed}p{play}", nrep=nrep, pos={str(J): v for J, v in m.items()}, s={str(J): v for J, v in s.items() if v > 1e-12})); continue
                rng.shuffle(sp); sp.sort(key=lambda d: -max(SP.popc(J) for J, v in d.items() if v > 1e-9))
                robust = None; tried = []
                for d in sp:
                    m2 = E.step(m, s, d, 1 << nrep)
                    sb, tg = break1(E, m2, nrep + 1, rng, iters, ncand)
                    if sb is None: robust = d; break
                    tried.append((d, sb))
                if robust is None:
                    nlev2 += 1
                    W(dict(LEVEL2=True, tag=f"s{seed}p{play}", nrep=nrep, target=target, nspoilers=len(sp), pos={str(J): v for J, v in m.items()},
                           s={str(J): v for J, v in s.items() if v > 1e-12},
                           lines=[dict(d={str(J): v for J, v in d.items() if v > 1e-12}, s2={str(J): v for J, v in sb.items() if v > 1e-12}) for d, sb in tried]))
                else:
                    nrob += 1; cont.append((s, robust, len(tried), len(sp)))
            W(dict(tag=f"s{seed}p{play}", nrep=nrep, ncells=len(m), vold=vold, nS=len(cs), level2=nlev2, refuted=nrob,
                   nonrobust_before_robust=[(a, b) for _, _, a, b in cont], secs=round(time.time() - t0), lps=E.nlp))
            if not cont: break
            s, d, _, _ = rng.choice(cont)
            m = E.step(m, s, d, 1 << nrep); nrep += 1
