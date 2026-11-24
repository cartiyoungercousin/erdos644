"""CORE Part IX (49): two-step-robust dumps.  At a position with nrep0 kept replies (reached by one-step-robust play),
for each request S his menu spoilers d are classified:
  robust1(d): her break1 fails after d;   robust2(d): robust1 and, at the position after d, every one of nS2 candidate
  requests S' has a robust1 spoiler (no two-request break found there).
A request S with no robust2 spoiler in his menu is a THREE-request break candidate (LEVEL3 line).
Usage: py spoil_three.py t N o seed nrep0 nS nS2 iters"""
import sys, json, random, time
import spoil as SP, spoil_hunt as H, spoil_two as TW

def robust1(E, m, nrep, rng, iters): return TW.break1(E, m, nrep, rng, iters, 20)[0] is None

def level2_break(E, m, nrep, rng, nS, iters):
    """a request at (m, nrep) all of whose menu spoilers are non-robust1, or None"""
    cs, vold = E.cands(m, nrep, rng); rng.shuffle(cs); cs = cs[:nS]; target = min(vold, E.base)
    for s in cs:
        sp = H.spoilers(E, m, nrep, s, target)
        if not sp: return s
        rng.shuffle(sp); sp.sort(key=lambda d: -max(SP.popc(J) for J, v in d.items() if v > 1e-9))
        if not any(robust1(E, E.step(m, s, d, 1 << nrep), nrep + 1, rng, iters) for d in sp): return s
    return None

if __name__ == "__main__":
    t, N, o = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    seed, nrep0, nS, nS2, iters = (int(x) for x in sys.argv[4:9])
    E = SP.Engine(t, N); rng = random.Random(seed); c = N - 1
    f = open(f"logs/three_t{t}_N{N}_s{seed}_n{nrep0}.log", "w")
    def W(d): f.write(json.dumps(d) + "\n"); f.flush()
    while True:
        m = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}; nrep = 2; dead = False
        while nrep < nrep0:                                   # one-step-robust play to the test position
            cs, vold = E.cands(m, nrep, rng); s = rng.choice(cs); target = min(vold, E.base)
            sp = H.spoilers(E, m, nrep, s, target); rng.shuffle(sp); sp.sort(key=lambda d: -max(SP.popc(J) for J, v in d.items() if v > 1e-9))
            nxt = next((d for d in sp if robust1(E, E.step(m, s, d, 1 << nrep), nrep + 1, rng, iters)), None)
            if nxt is None: dead = True; break
            m = E.step(m, s, nxt, 1 << nrep); nrep += 1
        if dead: continue
        cs, vold = E.cands(m, nrep, rng); rng.shuffle(cs); target = min(vold, E.base)
        for s in cs[:nS]:
            t0 = time.time(); sp = H.spoilers(E, m, nrep, s, target)
            rng.shuffle(sp); sp.sort(key=lambda d: -max(SP.popc(J) for J, v in d.items() if v > 1e-9))
            n1 = 0; found = None; tried = 0
            for d in sp:
                tried += 1; m2 = E.step(m, s, d, 1 << nrep)
                if not robust1(E, m2, nrep + 1, rng, iters): continue
                n1 += 1
                if level2_break(E, m2, nrep + 1, rng, nS2, iters) is None: found = d; break
            row = dict(nrep=nrep, spoilers=len(sp), tried=tried, robust1=n1, robust2=found is not None, secs=round(time.time() - t0))
            if found is None:
                row.update(LEVEL3=True, pos={str(J): v for J, v in m.items()}, s={str(J): v for J, v in s.items() if v > 1e-12})
            W(row)
