"""Stage-1 adversary search with the drop-one frames (exploratory adversary; every reported ADV is exact).
For a first request R1 after Theorem P's K (units k/14, alpha = 7, t = 12 - delta), look for an answer M1 that
  (i)  avoids R1, has mass 14 and is S*-legal against E, F, G, K;
  (ii) defeats every static drop-one finish: {F,G,K,M1}, {E,G,K,M1}, {E,F,K,M1}, {E,F,G,M1} with three requests
       (exact cell MILP, SCIP) all need more than t;
  (iii) is ADV in the joint-MILP E-frame game (jm.stage2: SCIP-proved infeasible master).
Candidates: jm.oracle1 min-drop answers under several weightings and pad preferences, voluntary drops, and random
legal answers on a 0.25 grid.  Output lines: {'R1', 'M1', 'static', 'stage2'}."""
import sys, os, json, time, random
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'jointmilp'))
import jm
from frames import base_sizes, refine, alive, ZEPS
from cover import min_t

S = jm.sizes(7.0); T = 12 - 0.002; C7 = jm.C7; SPEC = jm.SPEC
FR = {'FGKM1': (['F', 'G', 'K', 'M1'], 3), 'EGKM1': (['E', 'G', 'K', 'M1'], 3),
      'EFKM1': (['E', 'F', 'K', 'M1'], 3), 'EFGM1': (['E', 'F', 'G', 'M1'], 3)}


def legal(m, o):
    if abs(sum(m.values()) + o - 14) > 1e-6 or min(m.values()) < -1e-9 or o < -1e-9: return False
    return all(jm.in_spec(sum(m[c] for c in cs), SPEC, 1e-7) for cs in jm.MEM.values())


def static_vals(m, stop=None):
    mm = dict(m); mm['Z'] = ZEPS / 2
    at = refine(base_sizes(7.0), [{(c,): v for c, v in mm.items()}])
    sz = {a: s for a, s in at.items() if s > 1e-9}
    out = {}
    for nm, (fr, r) in FR.items():
        tt, _ = min_t(sz, alive(at, fr), r, tl=60)
        out[nm] = tt
        if stop is not None and (tt is None or tt <= stop): break
    return out


def candidates(r, rng, nrand):
    cand = []
    def add(m, o):
        key = tuple(round(m[c], 6) for c in C7) + (round(o, 6),)
        if key not in [k for k, _, _ in cand] and legal(m, o): cand.append((key, m, o))
    rd = dict(zip(C7, r))
    W = [None, {'X': 1, 'Y': 1, 'A': 1.3, 'B': 1.3}, {'X': 1.3, 'Y': 1.3, 'A': 1, 'B': 1},
         {'X': 1, 'Y': 1.3, 'A': 1.3, 'B': 1}, {'X': 1.3, 'Y': 1, 'A': 1, 'B': 1.3}]
    for w in W:
        for wpad in ({'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3}, {'Ep': -1e-3, 'Fd': -1e-3, 'Gd': -1e-3},
                     {'Ep': 1e-3, 'Fd': -1e-3, 'Gd': -1e-3}):
            o = jm.oracle1(S, rd, SPEC, w=w, wpad=wpad)
            if o is None: continue
            add(*o)
            m1, o1 = o
            for c in jm.L:
                for d in (0.25, 0.5, 1.0, 2.0):
                    if m1[c] >= d - 1e-9:
                        mm = dict(m1); mm[c] -= d; add(mm, o1 + d)
    avail = {c: S[c] - rd[c] for c in C7}
    for _ in range(nrand):
        m = {c: min(avail[c], round(rng.choice([0, 1, 1, 1]) * rng.uniform(0, avail[c]) * 4) / 4) for c in C7}
        if rng.random() < 0.5:
            for c in jm.L:
                if rng.random() < 0.6: m[c] = avail[c]
        tot = sum(m.values())
        if tot > 14:
            continue
        add(m, 14 - tot)
    return cand


def search(r, nrand=300, seed=0, max_stage2=6, log=print):
    rng = random.Random(seed); t0 = time.time()
    cand = candidates(r, rng, nrand)
    good = []
    for key, m, o in cand:
        sv = static_vals(m, stop=T + 1e-6)
        if len(sv) == len(FR) and all(v is not None and v > T + 1e-6 for v in sv.values()):
            good.append((min(sv.values()), key, m, o, sv))
    log('R1 %s: %d candidates, %d statically invulnerable (%.0fs)' % (r, len(cand), len(good), time.time() - t0))
    good.sort(key=lambda g: -sum(g[2][c] for c in jm.L))
    for g in good[:max_stage2]:
        _, key, m, o, sv = g
        res, info, it, _ = jm.stage2(S, m, o, T, SPEC, maxit=120, tl=100, wall=240)
        log('   M1 %s static %s -> stage2 %s (%d it, %.0fs)' % (key, {k: round(v, 3) for k, v in sv.items()}, res, it,
                                                              time.time() - t0))
        if res == 'ADV':
            cert = [[{'%s%d' % k: v for k, v in P.items() if v > 0}, PO] for P, PO in info]
            return {'R1': list(r), 'M1': list(key), 'static': sv, 'stage2': 'ADV', 'cert': cert}
    return {'R1': list(r), 'M1': None, 'n_static_ok': len(good), 'stage2': None}


if __name__ == '__main__':
    r = [float(x) for x in sys.argv[1].split(',')]
    out = search(r, nrand=int(sys.argv[2]) if len(sys.argv) > 2 else 300)
    print(json.dumps({k: v for k, v in out.items() if k != 'cert'}))
