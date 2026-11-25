r"""Local sharpness of Lemma P1 (PROGRAMME4_P1.md, Section 3).
Given a pencil x1,x2,x3 (k-sets, empty triple intersection) with regions E_i (only in x_i), D_ij (x_i & x_j),
union U, |U| = (3k+w)/2, Z = V \ U, z = |Z|, and T, r = n-k-T, let
    H_Z = { k-sets B : |B & Z| <= z - r }     (contains x1,x2,x3; T-covering; tau(H_Z) = T+1).
A good seven of H_Z containing x1,x2,x3 on the three lines through p0 = four members B_g (g in {000,011,101,110})
such that every U-point lies in <= 2 of them, and a U-point in B_g & B_h (g,h agreeing in coordinate i) is not in x_i
(Z-points: colour p0, no constraint).  By symmetry of H_Z this is an exact profile ILP over the regions.
Capacity: 4(k - z + r) <= 2|U| is necessary, i.e. w <= 4T-3k.  P1 gives sufficiency for w <= 4T-3k-6.
usage: p1_local.py kmin kmax      (scans T, n, w and several region splits; prints the exact threshold)"""
import sys, itertools, random
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds

G = [(0,0,0),(0,1,1),(1,0,1),(1,1,0)]
REG = ['E1','E2','E3','D12','D13','D23']
INX = {'E1':{0},'E2':{1},'E3':{2},'D12':{0,1},'D13':{0,2},'D23':{1,2}}   # which x_i (0-based) contain the region
def agree(g, h): return next(i for i in range(3) if G[g][i] == G[h][i])
def allowed(R):
    out = [()] + [(g,) for g in range(4)]
    for g, h in itertools.combinations(range(4), 2):
        if agree(g, h) not in INX[R]: out.append((g, h))
    return out
ZS = [S for m in range(5) for S in itertools.combinations(range(4), m)]

def complete(k, T, n, sizes):
    """sizes: dict region -> size.  Exact: is there a concurrent completion inside H_Z?"""
    u = sum(sizes.values()); z = n - u; r = n - k - T
    if z < r or r < 0: return None
    var = [(R, S) for R in REG for S in allowed(R)] + [('Z', S) for S in ZS]
    nv = len(var); A = []; lo = []; hi = []
    for R in REG + ['Z']:
        row = np.zeros(nv)
        for i, (Q, S) in enumerate(var):
            if Q == R: row[i] = 1
        A.append(row); c = z if R == 'Z' else sizes[R]; lo.append(c); hi.append(c)
    for g in range(4):
        row = np.zeros(nv); rz = np.zeros(nv)
        for i, (Q, S) in enumerate(var):
            if g in S:
                row[i] = 1
                if Q == 'Z': rz[i] = 1
        A.append(row); lo.append(k); hi.append(k)
        A.append(rz); lo.append(0); hi.append(z - r)
    res = milp(np.zeros(nv), constraints=LinearConstraint(np.array(A), lo, hi), integrality=np.ones(nv),
               bounds=Bounds(np.zeros(nv), np.full(nv, n)))
    if res.status == 0: return True
    if res.status == 2: return False
    raise RuntimeError(res.message)

def splits(k, w, rng, extra=4):
    """region sizes with x_i of size k and sum e_i = w: the balanced one plus random ones."""
    out = []
    def mk(e):
        D = 3 * k - sum(e)
        if D % 2: return None
        # d12 + d13 = k - e1, d12 + d23 = k - e2, d13 + d23 = k - e3
        t = (3 * k - sum(e)) // 2
        d23 = t - (k - e[0]); d13 = t - (k - e[1]); d12 = t - (k - e[2])
        if min(d12, d13, d23) < 0: return None
        return dict(E1=e[0], E2=e[1], E3=e[2], D12=d12, D13=d13, D23=d23)
    b = [w // 3 + (1 if i < w % 3 else 0) for i in range(3)]
    s = mk(b)
    if s: out.append(s)
    for _ in range(extra):
        c = sorted(rng.sample(range(w + 2), 2)); e = [c[0], c[1] - c[0] - 1, w - c[1] + 1]
        if min(e) >= 0:
            s = mk(e)
            if s: out.append(s)
    return out

def main(kmin, kmax):
    rng = random.Random(1); bad = 0; cnt = 0
    for k in range(kmin, kmax + 1):
        for T in range((3 * k) // 4 + 1, k):
            q = 4 * T - 3 * k
            for n in sorted({k + T + rr for rr in (0, 1, 2, 3, 5, 8, 12)} & set(range(k + T, 2 * k + 3))):
                r = n - k - T; thr = []
                for w in range(k % 2, 2 * T - k + 1, 2):
                    for sz in splits(k, w, rng):
                        ok = complete(k, T, n, sz)
                        if ok is None: continue
                        cnt += 1
                        if (ok and w > q) or (not ok and w <= q - 6): bad += 1; print('VIOLATION', k, T, n, sz, ok)
                        if ok: thr.append(w)
                if thr: print(f'k={k} T={T} n={n} r={r}: 4T-3k={q}, largest completable w in H_Z = {max(thr)}', flush=True)
    print(f'{cnt} instances, {bad} violations of [w <= 4T-3k-6 => completable] or [completable => w <= 4T-3k]')

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]))
