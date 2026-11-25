"""Brute-force sanity test of the relative pencil lemma NC-P (PROGRAMME5_COMPRESS Sec 2).
Instance: a random inclusion-minimal (k+d)-covering k-uniform family B on W = {0..w-1}, plus random k-sets meeting an
outside set Z (|Z| = z), so that tau(H) can exceed tau(B).  When the VERIFIED pencil-bound size conditions hold for
(w, k, d) and d+D <= 4T-3k-6 with the AMBIENT T = tau(H)-1, we check:
  (a) B has a pencil of weight <= d+D (exhaustive minimum over B),
  (b) the Lemma P1 colouring of that pencil yields seven members of H with no 2-point cover (brute force).
We also count 'relative' instances: those where P1 with the block's own T_B = tau(B)-1 would NOT apply.
Usage: py -3.14 ncp_test.py TRIALS SEED"""
import sys, random, itertools
import numpy as np
from ortools.sat.python import cp_model

def popc(x): return bin(x).count('1')

def tau(members, n):
    m = cp_model.CpModel(); x = [m.NewBoolVar('x%d' % i) for i in range(n)]
    for B in members: m.AddBoolOr([x[i] for i in range(n) if B >> i & 1])
    m.Minimize(sum(x)); s = cp_model.CpSolver(); s.parameters.num_workers = 1
    assert s.Solve(m) == cp_model.OPTIMAL
    return int(s.ObjectiveValue())

def D_of(k, d):
    w_ = max(0, -(-(d - 1) // 2))
    return w_ if (w_ - (k + d)) % 2 == 0 else w_ + 1

def min_cover_block(rng, w, k, d):
    mem = [sum(1 << i for i in c) for c in itertools.combinations(range(w), k)]
    sup = [sum(1 << i for i in c) for c in itertools.combinations(range(w), k + d)]
    inside = {B: [] for B in mem}; cnt = []
    for si, S in enumerate(sup):
        c = 0
        for B in mem:
            if B & S == B: inside[B].append(si); c += 1
        cnt.append(c)
    alive = set(mem); order = mem[:]; rng.shuffle(order)
    for B in order:
        if all(cnt[si] > 1 for si in inside[B]):
            alive.discard(B)
            for si in inside[B]: cnt[si] -= 1
    return sorted(alive)

def min_pencil(Bs):
    a = np.array(Bs, dtype=np.int64); best = None
    pc = np.vectorize(popc)
    for i in range(len(Bs)):
        for j in range(i, len(Bs)):
            x12 = Bs[i] & Bs[j]; s12 = Bs[i] ^ Bs[j]
            ok = (a & x12) == 0
            if not ok.any(): continue
            wts = pc((a[ok] ^ s12))
            t = int(wts.min())
            if best is None or t < best[0]:
                l = int(np.nonzero(ok)[0][int(wts.argmin())]); best = (t, Bs[i], Bs[j], Bs[l])
    return best

LINES_OFF0 = [(1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
Q = {1: (1, 2), 2: (3, 4), 3: (5, 6)}

def p1_seven(x, H, n):
    x1, x2, x3 = x; full = (1 << n) - 1; U = x1 | x2 | x3
    E = {1: x1 & ~x2 & ~x3, 2: x2 & ~x1 & ~x3, 3: x3 & ~x1 & ~x2}
    Dm = {3: x1 & x2, 2: x1 & x3, 1: x2 & x3}           # D_ij -> Q_m, m the third index
    col = [0] * n
    cls = {m: [] for m in (1, 2, 3)}
    for i in range(n):
        if not U >> i & 1: continue
        for m in (1, 2, 3):
            if Dm[m] >> i & 1: cls[m].append(i)
        for i_ in (1, 2, 3):
            if E[i_] >> i & 1: cls[i_ % 3 + 1].append(i)
    for m in (1, 2, 3):
        for t, i in enumerate(cls[m]): col[i] = Q[m][t % 2]
    seven = [x1, x2, x3]
    for ln in LINES_OFF0:
        L = sum(1 << i for i in range(n) if col[i] in ln and U >> i & 1)
        cand = [B for B in H if B & L == 0]
        if not cand: return None, popc(L)
        seven.append(cand[0])
    return seven, None

def has_2cover(seven, n):
    for p in range(n):
        for q in range(p, n):
            m = (1 << p) | (1 << q)
            if all(B & m for B in seven): return True
    return False

def main(trials, seed):
    rng = random.Random(seed)
    stats = dict(tested=0, relative=0, pencil_ok=0, seven_ok=0, fail=0)
    configs = [(4, 0, 7), (4, 0, 8), (4, 1, 9), (4, 1, 10), (5, 0, 9), (5, 0, 10), (4, 2, 12), (5, 1, 11)]
    for t in range(trials):
        k, d, w = rng.choice(configs); z = rng.randint(2, 6); n = w + z
        if not (3 * d <= 2 * k - 2 and 4 * (w - k - d) >= 2 * k + 5 * d + 3): continue
        Bs = min_cover_block(rng, w, k, d)
        rho = rng.choice([0.3, 0.5, 0.8, 1.0])
        out = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)
               if any(i >= w for i in c) and rng.random() < rho]
        H = Bs + out
        T = tau(H, n) - 1
        if d + D_of(k, d) > 4 * T - 3 * k - 6: continue
        stats['tested'] += 1
        TB = tau(Bs, w) - 1
        if d + D_of(k, d) > 4 * TB - 3 * k - 6: stats['relative'] += 1
        mp = min_pencil(Bs)
        if mp is None or mp[0] > d + D_of(k, d):
            stats['fail'] += 1; print('PENCIL FAIL', k, d, w, mp and mp[0]); continue
        stats['pencil_ok'] += 1
        seven, Lsz = p1_seven(mp[1:], H, n)
        if seven is None or has_2cover(seven, n):
            stats['fail'] += 1; print('SEVEN FAIL', k, d, w, z, T, Lsz); continue
        stats['seven_ok'] += 1
    print('trials=%d seed=%d %s' % (trials, seed, stats))

if __name__ == '__main__':
    main(int(sys.argv[1]), int(sys.argv[2]))
