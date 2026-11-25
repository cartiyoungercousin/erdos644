r"""PROGRAMME_2 Task 4 measurements for one family H (edges as int bitmasks).
(1) dim C(H), rho = min wt(a + C(H)), a in H   [exact: enumeration of the coset, or MILP]
(2) least wt(x1+x2+x3) over member triples with x1&x2&x3 = 0 (exact for <= 500 members, else upper bound from a
    deterministic sample; rho is a valid lower bound because a triple sum is an odd sum), vs 4T-3k with T = tau-1
(3) Fano-type good sevens (random balanced colourings, Lemma 2 test exact; coordinate descent on sum_p wt(s_p)) vs
    3(4n-7k) and 7 rho
(4) 'coset fraction' chain: best nontrivial F2 functional u (Walsh transform) and the subfamily on its majority side.
Usage as a module: measure(fam) -> dict."""
import sys, os, time, random
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'task1'))
from gf2 import *
from tau_star import Family, min_transversal_size

FANO = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
THRU = {p: [i for i, l in enumerate(FANO) if p in l] for p in range(7)}

def cosetinfo(M, n):
    B = reduced_basis(M ^ M[0], n); rho, wit = coset_min_weight(int(M[0]), B, n)
    return len(B), rho, B

def triple_search(M, n, rng, n1=150, n2=60):
    N = len(M); best = (10**9, None)
    def scan(x1, x2):
        nonlocal best
        cand = M[(M & (x1 & x2)) == 0]
        if len(cand) == 0: return
        w = pc(cand ^ (x1 ^ x2)); i = int(np.argmin(w))
        if w[i] < best[0]: best = (int(w[i]), (int(x1), int(x2), int(cand[i])))
    if N <= 500:
        for i in range(N):
            for j in range(i + 1, N): scan(M[i], M[j])
        return best[0], True
    for i in rng.sample(range(N), min(n1, N)):
        x1 = M[i]; inter = pc(M & x1); order = np.argsort(-inter, kind='stable')
        js = list(order[:n2 // 2]) + rng.sample(range(N), n2 // 2)
        for j in js:
            if int(M[j]) != int(x1): scan(x1, M[j])
    return best[0], False

def fano_search(M, n, rng, ncol=1500, want=30, restarts=3, tlimit=300):
    sizes = pc(M); t0 = time.time(); tried = ok = 0; res = []
    best = None
    while tried < ncol and ok < want and time.time() - t0 < tlimit:
        tried += 1
        perm = list(range(n)); rng.shuffle(perm)
        cls = [0] * 7
        for pos, v in enumerate(perm): cls[pos % 7] |= 1 << v
        cands = []
        for l in FANO:
            L = cls[l[0]] | cls[l[1]] | cls[l[2]]; c = M[(M & L) == 0]
            if len(c) == 0: break
            cands.append(c)
        if len(cands) < 7: continue
        ok += 1; cbest = None
        for _ in range(restarts):
            B = [int(c[rng.randrange(len(c))]) for c in cands]
            for _pass in range(30):
                changed = False
                for i in rng.sample(range(7), 7):
                    others = []
                    for p in FANO[i]:
                        o = 0
                        for j in THRU[p]:
                            if j != i: o ^= B[j]
                        others.append(o)
                    c = cands[i]; cost = sum(pc(c ^ o).astype(np.int32) for o in others)
                    m = int(cost.min()); idx = np.flatnonzero(cost == m); pick = int(c[idx[rng.randrange(len(idx))]])
                    cur = sum(pc(B[i] ^ o) for o in others)
                    if m < cur: B[i] = pick; changed = True
                if not changed: break
            sp = []
            for p in range(7):
                s = 0
                for j in THRU[p]: s ^= B[j]
                sp.append(pc(s))
            tot = sum(sp)
            if cbest is None or tot < cbest[0]: cbest = (tot, sp, list(B))
        res.append(cbest[0])
        if best is None or cbest[0] < best[0]: best = cbest
    if best is None: return dict(colourings_tried=tried, colourings_ok=0)
    B = best[2]; U = 0; S = 0
    for b in B: U |= b; S += pc(b)
    cnt = {}
    for b in B:
        for x in range(n):
            if (b >> x) & 1: cnt[x] = cnt.get(x, 0) + 1
    ident = sum(j * (4 - j) for j in cnt.values())
    assert ident == best[0], (ident, best[0])
    return dict(colourings_tried=tried, colourings_ok=ok, min_sum_wt=int(best[0]), pencil_wts=[int(x) for x in best[1]],
                union=pc(U), sum_sizes=int(S), lemma5_budget=int(3 * (4 * pc(U) - S)), min_over_colourings=int(min(res)),
                median_over_colourings=float(np.median(res)), sizes=sorted(set(int(x) for x in pc(np.array(B)))))

def coset_chain(M, n, depth=3):
    if n > 25: return None
    out = []; cur = M; N0 = len(M)
    for step in range(depth):
        if len(cur) < 4: break
        f = np.zeros(1 << n, np.int32); f[cur] = 1; hat = fwht(f); N = len(cur)
        n1 = (N - hat) // 2; frac = np.maximum(n1, N - n1) / N
        frac[0] = 0; frac[(n1 == 0) | (n1 == N)] = 0
        u = int(np.argmax(frac)); fr = float(frac[u]); del f, hat, n1, frac
        if fr == 0: break
        par = pc(cur & u) & 1; maj = int(par.sum() * 2 > len(cur)); sub = cur[par == maj]
        d, rho, _ = cosetinfo(sub, n)
        out.append(dict(u=[x for x in range(n) if (u >> x) & 1], local_frac=round(fr, 5), kept=round(len(sub) / N0, 5),
                        size=int(len(sub)), dim=d, rho=rho))
        cur = sub
    return out

def measure(fam, seed=1, fano=True, chain=True, tau=None):
    rng = random.Random(seed); M = fam.masks; n = fam.n; t0 = time.time()
    sizes = pc(M); ks = np.bincount(sizes); k = int(np.argmax(ks)); kmax = int(sizes.max())
    tau = tau if tau is not None else min_transversal_size(fam); T = tau - 1
    d, rho, B = cosetinfo(M, n)
    ts, exact = triple_search(M, n, rng)
    r = dict(name=fam.name, n=n, members=int(len(M)), k=k, k_sizes={int(s): int(c) for s, c in enumerate(ks) if c}, tau=tau, T=T,
             dim_C=d, rho=rho, codim=n - d, a_in_C=bool(rho == 0), rho_gt_4T3k=bool(rho > 4 * T - 3 * k),
             four_T_minus_3k=4 * T - 3 * k, triple_min=ts, triple_exact=exact, triple_lb_rho=rho,
             budget_3_4n_7k=3 * (4 * n - 7 * k), cor7=bool(7 * rho > 3 * (4 * n - 7 * k)))
    if chain: r['chain'] = coset_chain(M, n)
    if fano: r['fano'] = fano_search(M, n, rng)
    r['secs'] = round(time.time() - t0, 1)
    return r
