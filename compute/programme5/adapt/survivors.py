"""Which configurations does the S-game adversary use below 6/7, and do GENERAL one-request closures (depth1.py: any
request, any answer with traces in S*, exact 3-block finish or discard + t*_+) kill them where the lemma list fails?
usage: py -3.14 survivors.py G nu t [ntriples] [seed]
Prints S*, for each q in S* cap [0,t] the surviving answers to her best DUMP, then runs the general depth-1 search
(heuristic on both sides, see depth1.py) on a sample of surviving triples."""
import sys, random, itertools, numpy as np
import sgame, depth1

def surviving_answers(gm, S, t, nu, CL, qi):
    G, g = gm.G, gm.g
    q = g[qi]
    bad = (~CL[qi]) & gm.feas[qi] & S[:, None] & S[None, :] & ((g[:, None] + g[None, :]) >= 3 - q - nu - 1e-9)
    tot = 2 - t - q; best = None
    for i in range(G + 1):
        for (Y, Zv) in ((g[i], tot - g[i]), (tot - g[i], g[i])):
            if Y > 1 - q + 1e-9 or Zv > 1 - q + 1e-9 or Y < 1 - t - 1e-9 or Zv < 1 - t - 1e-9: continue
            Yi, Zi = int(np.floor(Y * G + 1e-9)), int(np.floor(Zv * G + 1e-9))
            ans = [(a, b) for a in range(Yi + 1) for b in range(Zi + 1) if bad[a, b]]
            if best is None or len(ans) < len(best[1]): best = ((Yi, Zi), ans)
    return best

def requests(cells, t, step):
    x, y, z = cells; tot = {'X': x, 'Y': y, 'Z': z, 'E': 1 - x - y, 'F': 1 - x - z, 'G': 1 - y - z}
    grid = lambda hi: [i * step for i in range(int(hi / step + 1e-9) + 1)]
    out = []
    # pair cells: each fully, or partially (multiples of step)
    for ux in sorted(set(grid(x) + [x])):
        for uy in sorted(set(grid(y) + [y])):
            for uz in sorted(set(grid(z) + [z])):
                r = t - ux - uy - uz
                if r < -1e-12: continue
                # private parts: split r over E,F,G on the step grid (respecting sizes); leftover -> unused
                for ue in grid(min(r, tot['E'])):
                    for uf in grid(min(r - ue, tot['F'])):
                        ug = min(r - ue - uf, tot['G'])
                        out.append({'X': ux, 'Y': uy, 'Z': uz, 'E': ue, 'F': uf, 'G': ug})
    return out

if __name__ == '__main__':
    G, nu, t = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    ntri = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 0)
    T3 = sgame.load_static(G); gm = sgame.Game(G, T3)
    adv, S, (CL, lem, Hv) = sgame.solve(G, T3, nu, t, game=gm)
    print('t=%.5f nu=%g G=%d: %s  S*=%s' % (t, nu, G, 'ADVERSARY' if adv else 'REQUESTER', sgame.compact(S, G)), flush=True)
    pool = []
    for qi in range(G):
        if not S[qi] or gm.g[qi] > t: continue
        box, ans = surviving_answers(gm, S, t, nu, CL, qi)
        print('  q=%d/%d best box (%d,%d): %d surviving answers, e.g. %s' % (qi, G, box[0], box[1], len(ans), ans[:6]), flush=True)
        pool += [(qi, a, b) for (a, b) in ans]
    inS = lambda v: S[min(G, int(round(v * G)))] and abs(v * G - round(v * G)) < 1e-6
    for (qi, a, b) in rng.sample(pool, min(ntri, len(pool))):
        cells = (gm.g[qi], gm.g[a], gm.g[b])
        best = None
        for U in requests(cells, t, 1 / 12):
            r = depth1.spoil(cells, U, t, inS, rng, G=G, tries=40)
            if r is not None and len(r) == 3 and r[1] <= t + 1e-9:
                best = (U, r[1]); break
        print('  triple %s: general depth-1 closure %s' % (tuple(round(c, 4) for c in cells),
              'FOUND (heuristic adversary) U=%s val=%.4f' % best if best else 'not found'), flush=True)
