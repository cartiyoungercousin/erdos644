"""Experiment E2: NON-LINEAR unions of cosets ("deep-class families").
Code C of length n <= 24 (punctured / shortened RM(2,5), or cyclic). Every vector gets its coset; coset weight
cw(v) = min weight in v + C. Family H(k, w0) = { k-sets B : cw(B) >= w0 }. The class set T = {cw >= w0} is
not an affine subspace, so H is not a coset family. Invariant under Aut(C).
usage: py -3.14 deep_union.py CODE w0 [kmin kmax]
"""
import sys, json, time
import numpy as np
from tools import tau_ilp, triple_stats, seven_sat, check_seven, popcount64
from coset_fams import rm_gen, span

def echelon(rows):
    piv = []
    for r in rows:
        for p, b in piv:
            if r >> p & 1: r ^= b
        if r:
            p = r.bit_length() - 1
            piv = [(q, b ^ r if b >> p & 1 else b) for q, b in piv] + [(p, r)]
    return piv

def puncture(rows, n, keep):
    out = []
    for r in rows:
        out.append(sum(1 << j for j, i in enumerate(keep) if r >> i & 1))
    return out, len(keep)

def shorten(rows, n, drop):
    # codewords vanishing on drop, then delete drop
    piv = echelon(rows); basis = [b for _, b in piv]
    # eliminate coordinates in drop
    sub = basis
    for d in drop:
        withd = [b for b in sub if b >> d & 1]; wo = [b for b in sub if not b >> d & 1]
        if withd:
            h = withd[0]; sub = wo + [b ^ h for b in withd[1:]]
    keep = [i for i in range(n) if i not in drop]
    return puncture(sub, n, keep)

CODES = {
    'prm24': lambda: puncture(*rm_gen(2, 5), list(range(24))),          # [24,16] punctured RM(2,5)
    'srm24': lambda: shorten(*rm_gen(2, 5), list(range(24, 32))),      # shortened RM(2,5) to length 24
    'prm22': lambda: puncture(*rm_gen(2, 5), list(range(22))),
    'srm22': lambda: shorten(*rm_gen(2, 5), list(range(22, 32))),
}

def main(name, w0, kmin=None, kmax=None, budget=400_000):
    rows, n = CODES[name]()
    piv = echelon([r for r in rows if r])
    dim = len(piv)
    V = np.arange(1 << n, dtype=np.uint32)
    rep = V.copy()
    for p, b in sorted(piv, reverse=True):
        mask = (rep >> np.uint32(p)) & np.uint32(1)
        rep ^= mask * np.uint32(b)
    wt = popcount64(V.astype(np.uint64)).astype(np.int8)
    cw = np.full(1 << n, 127, dtype=np.int8)
    np.minimum.at(cw, rep, wt)
    cwv = cw[rep]
    hist = np.bincount(cw[cw < 127].astype(np.int64))
    print(f'{name}: n={n} dim={dim} codim={n-dim} coset-weight histogram {hist.tolist()}', flush=True)
    kmin = kmin or int(np.ceil(n / 1.95)); kmax = kmax or int(n / 1.72)
    for k in range(kmin, kmax + 1):
        sel = (wt == k) & (cwv >= w0)
        fam = [int(v) for v in V[sel]]
        if not fam:
            print(json.dumps(dict(code=name, n=n, k=k, w0=w0, M=0))); continue
        t0 = time.time()
        tau, lb, st = tau_ilp(fam, n, 60)
        W, P, ex = triple_stats(fam, maxpairs=20_000)
        res, sv = ('SKIP', None)
        if len(fam) <= 15000:
            res, sv = seven_sat(fam, n, budget)
            if sv: assert check_seven(sv, n)
        print(json.dumps(dict(code=name, n=n, k=k, N=round(n / k, 3), w0=w0, M=len(fam), tau=tau, tau_lb=lb,
                              status=st, excess=tau - 0.75 * k, W=W, P=P, exact_WP=ex,
                              lemmaQ_thr=round((12 * n - 21 * k) / 7, 2), seven=res,
                              secs=round(time.time() - t0, 1))), flush=True)

if __name__ == '__main__':
    a = sys.argv
    main(a[1], int(a[2]), *(int(x) for x in a[3:5]))
