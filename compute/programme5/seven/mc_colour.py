"""Programme 5 (seven): level profiles of the member-free down-set D and random / adapted Fano colourings.

For a family H (k-sets on n points) we report
  * phi(m) = P(random m-set contains a member) = 1 - mu(m), exact for every level m (explicit families: full
    up-set table over 2^n; predicate families: exact hypergeometric sums);
  * iid colourings chi: V -> F_2^3 \\ {0} (uniform), and balanced colourings (class sizes as equal as possible):
    marginals P(R_u in U), the union-bound value sum_u mu, the independence prediction prod_u P(R_u in U), the
    joint success rate cert = P(all seven R_u in U), and the 7-term correlation index kappa = log10(cert / prod);
  * adapted colourings: (A) anchored on a random member B (B forced into R_u0), (P) P1-pencil colourings with
    random splits (Z -> c0, D_ij -> Q_m, E_i -> Q_{i+1}), success of the four non-pencil lines.
Colour c, line u: R_u = {p : <c(p), u> = 1}.
Usage: py -3.14 mc_colour.py SPEC [samples] [seed]
  SPEC: file:PATH:n:k  (npy of member bitmasks) | fkw:m | complete:n:k | thresh:n:k:a:t ({B : |B cap A| >= t})
        | covrand:n:k:r:seed (random binomial family at density ~ 1.5 ln C(n,k+r)/C(k+r,r), then patched to cover)
"""
import sys
import numpy as np
from math import comb, log10

PAR = np.array([bin(x).count('1') & 1 for x in range(8)], dtype=np.uint8)
PC8 = np.array([bin(x).count('1') for x in range(256)], dtype=np.uint8)


def popcount(a):
    a = a.astype(np.uint64)
    s = np.zeros(a.shape, dtype=np.int64)
    for sh in range(0, 64, 8):
        s += PC8[((a >> np.uint64(sh)) & np.uint64(255)).astype(np.int64)]
    return s


def upset_table(n, members):
    U = np.zeros(1 << n, dtype=bool)
    U[np.asarray(members, dtype=np.int64)] = True
    for i in range(n):
        V = U.reshape(-1, 2, 1 << i)
        V[:, 1, :] |= V[:, 0, :]
    return U


class Explicit:
    def __init__(self, n, k, members, name):
        self.n, self.k, self.name = n, k, name
        self.M = np.unique(np.asarray(members, dtype=np.int64))
        self.U = upset_table(n, self.M)
        pc = popcount(np.arange(1 << n, dtype=np.int64))
        self.phi = {m: float(self.U[pc == m].mean()) for m in range(k, n + 1)}
        self.cover = min(m for m in range(k, n + 1) if self.phi[m] == 1.0)

    def good(self, R):
        return self.U[R]

    def rand_member(self, rng):
        return int(self.M[rng.integers(len(self.M))])


class Pred:
    """Families given by a predicate on trace sizes (FKW, complete, threshold)."""

    def __init__(self, kind, n, k, A_size=0, t=0):
        self.kind, self.n, self.k, self.a, self.t = kind, n, k, A_size, t
        self.Amask = (1 << A_size) - 1
        self.name = {'fkw': 'FKW n=%d k=%d |X|=%d' % (n, k, A_size), 'complete': 'K_%d^(%d)' % (n, k),
                     'thresh': 'thresh n=%d k=%d |A|=%d t=%d' % (n, k, A_size, t)}[kind]
        self.phi = {}
        for m in range(k, n + 1):
            tot = 0
            for x in range(max(0, m - (n - self.a)), min(m, self.a) + 1):
                if self.ok(x, m - x):
                    tot += comb(self.a, x) * comb(n - self.a, m - x)
            self.phi[m] = tot / comb(n, m)
        self.cover = min(m for m in range(k, n + 1) if self.phi[m] == 1.0)
        self.tab = np.array([[self.ok(x, y) for y in range(n - self.a + 1)] for x in range(self.a + 1)], dtype=bool)

    def ok(self, x, y):
        k = self.k
        if x + y < k:
            return False
        if self.kind == 'complete':
            return True
        if self.kind == 'thresh':
            return x >= self.t
        lo, hi = max(1, k - y), min(x, k - 1)   # fkw: odd a' in [lo, hi], k even
        if lo % 2 == 0:
            lo += 1
        return lo <= hi

    def good(self, R):
        x = popcount(R & self.Amask)
        y = popcount(R) - x
        return self.tab[x, y]

    def rand_member(self, rng):
        n, k = self.n, self.k
        while True:
            S = rng.choice(n, size=k, replace=False)
            m = int(sum(1 << int(i) for i in S))
            x = bin(m & self.Amask).count('1')
            if self.ok(x, k - x):
                return m


def r_masks(col, n):
    """col: (B, n) colours in 0..7 -> (7, B) masks of R_u, u = 1..7."""
    w = (np.int64(1) << np.arange(n, dtype=np.int64))
    out = []
    for u in range(1, 8):
        bits = PAR[col & u]
        out.append((bits.astype(np.int64) * w).sum(axis=1))
    return np.array(out)


def run_colourings(F, col):
    R = r_masks(col, F.n)
    G = np.array([F.good(R[u]) for u in range(7)])
    marg = G.mean(axis=1)
    joint = G.all(axis=0).mean()
    sizes = popcount(R).mean(axis=1)
    return marg, joint, sizes


def report(F, S, rng):
    n, k = F.n, F.k
    T = n - F.cover
    r = F.cover - k
    m4 = (4 * n) // 7
    out = []
    out.append('== %s  (n=%d k=%d; covering level k+r=%d, r=%d, T=%d, 4T-3k=%d, 4n/7=%.2f)' % (
        F.name, n, k, F.cover, r, T, 4 * T - 3 * k, 4 * n / 7))
    out.append('   phi(m)=P(m-set contains member): ' + ' '.join('%d:%.3g' % (m, F.phi[m]) for m in range(k, F.cover + 1)))
    out.append('   union bound at balanced sizes: sum_u mu(|R_u|) = %.3f (a seven is certified if < 1)' % (
        sum(1 - F.phi.get(s, 0.0) for s in balanced_sizes(n))))
    # iid colourings
    col = rng.integers(1, 8, size=(S, n)).astype(np.uint8)
    marg, joint, sizes = run_colourings(F, col)
    out.append(fmt('iid', marg, joint))
    # balanced colourings
    base = np.array([1 + (i % 7) for i in range(n)], dtype=np.uint8)
    col = np.array([rng.permutation(base) for _ in range(S)], dtype=np.uint8)
    marg, joint, sizes = run_colourings(F, col)
    out.append(fmt('balanced', marg, joint))
    # anchored on a random member
    col = rng.integers(1, 8, size=(S, n)).astype(np.uint8)
    good4 = {u0: np.array([c for c in range(1, 8) if PAR[c & u0]], dtype=np.uint8) for u0 in range(1, 8)}
    for s in range(S):
        B = F.rand_member(rng)
        u0 = 1 + (s % 7)
        idx = [i for i in range(n) if B >> i & 1]
        col[s, idx] = good4[u0][rng.integers(4, size=len(idx))]
    marg, joint, sizes = run_colourings(F, col)
    out.append(fmt('anchored', marg, joint))
    return out


def balanced_sizes(n):
    q, rem = divmod(n, 7)
    cls = [q + (1 if i < rem else 0) for i in range(7)]
    return [sum(cls[c - 1] for c in range(1, 8) if PAR[c & u]) for u in range(1, 8)]


def fmt(tag, marg, joint):
    prod = float(np.prod(marg))
    kap = (log10(joint / prod) if joint > 0 and prod > 0 else float('-inf'))
    return '   %-9s marg min/mean %.4f/%.4f  sum mu %.3f  prod %.3e  cert %.3e  kappa=log10(cert/prod) %s' % (
        tag, marg.min(), marg.mean(), float((1 - marg).sum()), prod, joint,
        ('%.2f' % kap) if kap != float('-inf') else ('-inf' if prod > 0 else 'n/a'))


def pencil_test(F, rng, pairs=300, S=20000):
    """P1-adapted colourings with random splits on the lightest pencils found by sampling."""
    if not isinstance(F, Explicit):
        return []
    n, k, M = F.n, F.k, F.M
    pcM = None
    best = []
    for _ in range(pairs):
        x1, x2 = int(M[rng.integers(len(M))]), int(M[rng.integers(len(M))])
        I = x1 & x2
        cand = M[(M & I) == 0]
        if len(cand) == 0:
            continue
        w = popcount(cand ^ (x1 ^ x2))
        j = int(np.argmin(w))
        best.append((int(w[j]), x1, x2, int(cand[j])))
    best.sort()
    T = n - F.cover
    out = ['   P1 threshold 4T-3k-6 = %d; lightest pencil weights found: %s' % (
        4 * T - 3 * k - 6, sorted(set(b[0] for b in best))[:8])]
    seen = set()
    for w, x1, x2, x3 in best:
        if len(seen) >= 4:
            break
        if w in seen:
            continue
        seen.add(w)
        # colours: c0 = 1; pencil lines u1=2,u2=4,u3=6; Q_1={4,5}, Q_2={2,3}, Q_3={6,7}
        Q = {1: (4, 5), 2: (2, 3), 3: (6, 7)}
        xs = (x1, x2, x3)
        col = np.zeros((S, n), dtype=np.uint8)
        for p in range(n):
            ins = [i for i in range(3) if xs[i] >> p & 1]
            if not ins:
                col[:, p] = 1
            elif len(ins) == 2:
                m = 6 - (ins[0] + 1) - (ins[1] + 1)
                col[:, p] = np.array(Q[m], dtype=np.uint8)[rng.integers(2, size=S)]
            else:
                m = (ins[0] + 1) % 3 + 1
                col[:, p] = np.array(Q[m], dtype=np.uint8)[rng.integers(2, size=S)]
        R = r_masks(col, n)
        ok3 = all(((R[u - 1] & xs[i]) == xs[i]).all() for i, u in enumerate((2, 4, 6)))
        others = [u for u in range(1, 8) if PAR[1 & u]]
        G = np.array([F.good(R[u - 1]) for u in others])
        out.append('   pencil w=%d (|Z|=%d): pencil lines contain x_i: %s; 4 other lines marg %s joint %.3e' % (
            w, n - bin(x1 | x2 | x3).count('1'), ok3, ' '.join('%.3f' % v for v in G.mean(axis=1)),
            G.all(axis=0).mean()))
    return out


def build(spec):
    p = spec.split(':')
    if p[0] == 'file':
        n, k = int(p[2]), int(p[3])
        return Explicit(n, k, np.load(p[1]), p[1].split('/')[-1].split('\\')[-1])
    if p[0] == 'fkw':
        m = int(p[1])
        return Pred('fkw', 7 * m + 1, 4 * m, 4 * m)
    if p[0] == 'complete':
        return Pred('complete', int(p[1]), int(p[2]))
    if p[0] == 'thresh':
        return Pred('thresh', int(p[1]), int(p[2]), int(p[3]), int(p[4]))
    if p[0] == 'covrand':
        n, k, r, seed = map(int, p[1:5])
        rng = np.random.default_rng(seed)
        from math import log
        dens = 1.5 * log(comb(n, k + r)) / comb(k + r, r)
        allk = np.array([sum(1 << i for i in c) for c in combos(n, k)], dtype=np.int64)
        M = allk[rng.random(len(allk)) < dens]
        pc = popcount(np.arange(1 << n, dtype=np.int64))
        while True:
            U = upset_table(n, M)
            unc = np.nonzero((~U) & (pc == k + r))[0]
            if len(unc) == 0:
                break
            add = []
            for S in unc[:2000]:
                bits = [i for i in range(n) if S >> i & 1]
                drop = rng.choice(len(bits), size=r, replace=False)
                add.append(int(S) - sum(1 << bits[d] for d in drop))
            M = np.concatenate([M, np.array(add, dtype=np.int64)])
        return Explicit(n, k, M, 'covrand n=%d k=%d r=%d seed=%d |H|=%d' % (n, k, r, seed, len(np.unique(M))))
    raise ValueError(spec)


def combos(n, k):
    from itertools import combinations
    return combinations(range(n), k)


def main():
    spec = sys.argv[1]
    S = int(sys.argv[2]) if len(sys.argv) > 2 else 200000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    rng = np.random.default_rng(seed)
    F = build(spec)
    lines = report(F, S, rng) + pencil_test(F, rng)
    print('\n'.join(lines), flush=True)


if __name__ == '__main__':
    main()
