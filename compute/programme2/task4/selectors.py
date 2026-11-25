r"""Task 4 (4): are the SAT-found pencil-free selectors affine over F2?
A selector sigma maps each T-set S (as a 0/1 vector 1_S in F2^n) to a class in {0..R-1}; 'affine' means (R = 2)
sigma(S) = c0 + <c, 1_S> for some c0 in F2, c in F2^n.
Two tests per case:
  (a) take the selector produced by core9/decide_family.build (the stored model) and compute its best affine agreement
      by a Walsh transform: max_u |sum_S (-1)^(sigma(S) + <u,1_S>)| / C(n,T)  (1 = exactly affine; ~0 = uncorrelated);
  (b) EXACT: add 'sigma is affine' to the pencil-free SAT instance of two_ground_sat.py (XOR-chain encoding) and solve.
      SAT = a pencil-free AFFINE selector exists for these orders.
Usage: py -3.14 selectors.py k T n R mode [seed] [skip_affine_sat]"""
import sys, os, json, itertools, random, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
CORE9 = os.path.abspath(os.path.join(HERE, '..', '..', 'core9')); sys.path.insert(0, CORE9)
from gf2 import fwht, pc
import decide_family as D
from two_ground_sat import three_partitions, mask
from pysat.solvers import Cadical153

def agreement(sel, n, R):
    keys = list(sel.keys()); cls = np.array([sel[m] for m in keys])
    if R == 2:
        f = np.zeros(1 << n, np.int32); f[np.array(keys, dtype=np.int64)] = 1 - 2 * cls
        h = fwht(f); u = int(np.argmax(np.abs(h))); return dict(best_affine_agreement=float((len(keys) + abs(h[u])) / 2 / len(keys)), u=[x for x in range(n) if (u >> x) & 1], const_class_share=float(max((cls == 0).mean(), (cls == 1).mean())))
    # R = 3: best affine 2-colouring of 'class 0 vs rest', 'class 1 vs rest', 'class 2 vs rest'
    out = {}
    for c in range(R):
        f = np.zeros(1 << n, np.int32); f[np.array(keys, dtype=np.int64)] = 1 - 2 * (cls == c)
        h = fwht(f); u = int(np.argmax(np.abs(h))); out[f'class{c}_vs_rest'] = dict(share=float((cls == c).mean()), best_affine_agreement=float((len(keys) + abs(h[u])) / 2 / len(keys)))
    return out

def affine_sat(k, T, n, R, mode, seed=0):
    om = n - k - T; ker = n - 3 * k // 2; h = k // 2; rng = random.Random(seed)
    if mode == 'rev': orders = [list(range(n)), list(range(n - 1, -1, -1))][:R]
    else: orders = [rng.sample(range(n), n) for _ in range(R)]
    s = Cadical153(); nv = 0; mem = {}
    def new():
        nonlocal nv; nv += 1; return nv
    def mv(K):
        if K not in mem: mem[K] = new()
        return mem[K]
    cx = [new() for _ in range(n)]; c0 = new()
    def xor(a, b):  # returns var y = a xor b
        y = new(); s.add_clause([-y, a, b]); s.add_clause([-y, -a, -b]); s.add_clause([y, -a, b]); s.add_clause([y, a, -b]); return y
    for S in itertools.combinations(range(n), T):
        ms = mask(S); Ks = []
        for o in orders:
            K = ms; c = 0
            for x in o:
                if not (ms >> x) & 1:
                    K |= 1 << x; c += 1
                    if c == om: break
            Ks.append(K)
        y = c0
        for x in S: y = xor(y, cx[x])
        s.add_clause([-y, mv(Ks[1])]); s.add_clause([y, mv(Ks[0])])     # y = 1 -> class 1 member, y = 0 -> class 0 member
    for kap in itertools.combinations(range(n), ker):
        mk = mask(kap); X = [x for x in range(n) if not (mk >> x) & 1]
        for P in three_partitions(X, h):
            L = [mk | mask(p) for p in P]
            if all(l in mem for l in L): s.add_clause([-mem[l] for l in L])
    t0 = time.time(); ok = s.solve()
    return ok, round(time.time() - t0)

if __name__ == '__main__':
    a = sys.argv; k, T, n, R = map(int, a[1:5]); mode = a[5]; seed = int(a[6]) if len(a) > 6 else 0
    fam, sel, orders = D.build(k, T, n, R, mode, seed)
    r = dict(case=f'k={k} T={T} n={n} R={R} {mode} seed={seed}', members=len(fam), T_sets=len(sel), classes={c: sum(1 for v in sel.values() if v == c) for c in range(R)})
    r.update(agreement(sel, n, R))
    if R == 2 and not (len(a) > 7 and a[7] == '1'):
        ok, secs = affine_sat(k, T, n, R, mode, seed); r['affine_pencil_free_selector_exists'] = ok; r['affine_sat_secs'] = secs
    print(json.dumps(r), flush=True); open(os.path.join(HERE, 'out', 'selectors.jsonl'), 'a').write(json.dumps(r) + '\n')
