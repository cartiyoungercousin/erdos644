r"""PROGRAMME 3 Task B (decision point D3): minimise Fano-type good sevens over T-covering families, track structure.

Convention (as PROGRAMME2 Task 4): H is a family of k-subsets of V, |V| = n; H is T-covering iff tau(H) > T iff every
(n-T)-subset of V contains a member.  Put s = n - T - k >= 0 (s = 0 forces the complete family).

Seven count.  For a colouring chi: V -> Fano points, L_l = chi^{-1}(l) and N_l(chi) = #{B in H : B cap L_l = {}}.
  W(H) = sum_chi prod_l N_l(chi) = #{(chi, (B_l)_l) : B_l cap L_l = {}}   (labelled Fano-type good sevens, each weighted
by its number of compatible colourings; W = 0 iff H has no Fano-type good seven).  W / 7^n = E_chi prod_l N_l is estimated
on a fixed panel of uniform random colourings (train panel = SA objective; an independent test panel is used for all
reported numbers).  'cert' = fraction of test colourings with min_l N_l >= 1 (each such colouring certifies a seven).
[heuristic: Monte Carlo estimate]

Search: simulated annealing.  Move = add a non-member B_in (a neighbour B - x + y of a random member), then delete, in random
order, every member that became redundant among those sharing an (n-T)-superset with B_in; Metropolis on the relative
change of the train objective (train panel resampled every 3000 moves).  Covering is maintained exactly (count array over (n-T)-sets).

usage: taskb.py k T n start seed minutes [P]      start in {random, layer:<spec>, complete, randlayer:<r>}"""
import sys, os, json, time, math, itertools
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'programme2', 'task4'))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'programme2', 'task1'))
from gf2 import reduced_basis, coset_min_weight

FANO = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
_T16 = np.array([bin(i).count('1') for i in range(1 << 16)], dtype=np.int8)
def pc(a):
    a = np.asarray(a, dtype=np.int64)
    return (_T16[a & 0xFFFF].astype(np.int16) + _T16[(a >> 16) & 0xFFFF] + _T16[(a >> 32) & 0xFFFF])

def ksets(n, k):
    out = np.zeros(math.comb(n, k), dtype=np.int64)
    for i, c in enumerate(itertools.combinations(range(n), k)):
        out[i] = sum(1 << x for x in c)
    return out

def fwht(a):
    a = a.astype(np.float64).copy(); h = 1; N = len(a)
    while h < N:
        a = a.reshape(-1, 2, h); x = a[:, 0, :].copy(); y = a[:, 1, :]
        a[:, 0, :] = x + y; a[:, 1, :] = x - y; a = a.reshape(N); h *= 2
    return a

def zeta_sub(g, n):
    g = g.copy()
    for i in range(n):
        v = g.reshape(-1, 2, 1 << i); v[:, 1, :] += v[:, 0, :]
    return g

class State:
    def __init__(self, k, T, n, rng):
        self.k, self.T, self.n = k, T, n; self.s = n - T - k; assert self.s >= 0
        self.full = (1 << n) - 1; self.rng = rng
        self.cnt = np.zeros(1 << n, np.uint16)       # members inside each (k+s)-set
        self.inH = np.zeros(1 << n, bool)
        self.mem = []; self.pos = {}
        self.ccomb = np.array(list(itertools.combinations(range(n - k), self.s)), dtype=np.int64).reshape(-1, self.s)
        self.subk = np.array(list(itertools.combinations(range(k + self.s), k)), dtype=np.int64)   # k-subsets of a (k+s)-set
    def bits_of(self, m): return np.array([1 << x for x in range(self.n) if m >> x & 1], dtype=np.int64)
    def bits_off(self, m): return np.array([1 << x for x in range(self.n) if not m >> x & 1], dtype=np.int64)
    def sup(self, B):
        if self.s == 0: return np.array([B], dtype=np.int64)
        return B | self.bits_off(B)[self.ccomb].sum(1)
    def add(self, B):
        self.inH[B] = True; self.pos[B] = len(self.mem); self.mem.append(B); np.add.at(self.cnt, self.sup(B), 1)
    def remove(self, B):
        self.inH[B] = False; i = self.pos.pop(B); last = self.mem.pop()
        if last != B: self.mem[i] = last; self.pos[last] = i
        np.subtract.at(self.cnt, self.sup(B), 1)
    def removable(self, B): return bool(self.cnt[self.sup(B)].min() >= 2)
    def covering(self):
        allS = ksets(self.n, self.k + self.s); return bool(self.cnt[allS].min() >= 1)
    def reduce_random(self):
        order = list(self.mem); self.rng.shuffle(order); r = 0
        for B in order:
            if self.removable(B): self.remove(B); r += 1
        return r
    def members(self): return np.array(self.mem, dtype=np.int64)
    def near_members(self, B):
        """members sharing a (k+s)-superset with B (excluding B)."""
        S = self.sup(B)
        if self.s == 0: return []
        cand = np.unique(np.concatenate([self._ksub(x) for x in S]))
        cand = cand[self.inH[cand]]; return [int(c) for c in cand if c != B]
    def _ksub(self, S):
        b = self.bits_of(S); return b[self.subk].sum(1)

class Panel:
    def __init__(self, n, c, P, rng):
        Ls = []; tried = 0
        while len(Ls) < P:
            m = 20000; tried += m
            chi = rng.integers(0, 7, size=(m, n))
            Lm = np.zeros((m, 7), np.int64)
            for l, line in enumerate(FANO):
                on = np.isin(chi, line)
                Lm[:, l] = (on.astype(np.int64) << np.arange(n, dtype=np.int64)).sum(1)
            ok = (pc(Lm) <= c).all(1); Ls.append(Lm[ok])
            Ls = [np.concatenate(Ls)]
            if len(Ls[0]) >= P: break
        self.adm = len(Ls[0]) / tried
        self.Lm = Ls[0][:P]; self.P = len(self.Lm)
    def N_of(self, members, n):
        g = np.zeros(1 << n, np.int32); g[members] = 1; g = zeta_sub(g, n)
        return g[((1 << n) - 1) ^ self.Lm].astype(np.int64)
    def fit(self, B): return ((self.Lm & B) == 0)
    def stats(self, N):
        pr = N.astype(np.float64).prod(1)
        return dict(mean_prod=float(pr.mean()) * self.adm, cert=float((N.min(1) >= 1).mean()) * self.adm)

# ---------------- measures ----------------
def measures(st, layerF, full_tau=False):
    n, k = st.n, st.k; M = st.members(); m = len(M)
    f = np.zeros(1 << n); f[M] = 1; F = fwht(f)
    allones = (1 << n) - 1
    u = np.arange(1 << n, dtype=np.int64); w = pc(u)
    out = dict(size=m)
    B = reduced_basis(M ^ M[0], n); out['dimC'] = len(B); out['codimC'] = n - len(B)
    out['rho'] = int(coset_min_weight(int(M[0]), B, n)[0]) if len(B) <= 22 else None
    for ww in (1, 2, 3, 4):
        sel = w == ww; out[f'four_w{ww}'] = float(np.abs(F[sel]).max() / m)
        out[f'four_w{ww}_complete'] = float(np.abs(layerF[sel]).max() / layerF[0])
    # best coset of codim r (beyond the trivial all-ones check), r = 1, 2, 3 via top functionals
    A = np.abs(F).copy(); A[0] = -1; A[allones] = -1
    top = np.argsort(-A)[:200]
    best1 = top[0]; p1 = (1 + A[best1] / m) / 2
    sgn1 = 1 if F[best1] >= 0 else -1
    d1 = (layerF[0] + sgn1 * layerF[best1]) / 2
    out.update(prop1=float(p1), u1_wt=int(w[best1]), dens1=float(p1 * m / d1) if d1 else None)
    def cells(us):
        # proportion in the best cell of span(us): max over sign patterns of E prod
        r = len(us); sub = [0]
        for x in us: sub = sub + [y ^ x for y in sub]
        if any(y in (0, allones) for y in sub[1:]): return -1, None
        best = (-1, None)
        for eps in itertools.product((1, -1), repeat=r):
            # sign of subspace element = product of eps over its generators
            tot = 0.0; lay = 0.0
            for idx, y in enumerate(sub):
                sg = 1
                for j in range(r):
                    if idx >> j & 1: sg *= eps[j]
                tot += sg * F[y]; lay += sg * layerF[y]
            if tot > best[0]: best = (tot, lay)
        return best[0] / (1 << r) / m, best[1] / (1 << r)
    p2 = (-1, None, None)
    for a, b in itertools.combinations(top[:120], 2):
        v, lay = cells([int(a), int(b)])
        if v > p2[0]: p2 = (v, lay, (int(w[a]), int(w[b])))
    p3 = (-1, None)
    t3 = top[:40]
    for a, b, c in itertools.combinations(t3, 3):
        v, lay = cells([int(a), int(b), int(c)])
        if v > p3[0]: p3 = (v, lay)
    out.update(prop2=float(p2[0]), dens2=float(p2[0] * m / p2[1]) if p2[1] else None, u2_wts=p2[2],
               prop3=float(p3[0]), dens3=float(p3[0] * m / p3[1]) if p3[1] else None)
    if full_tau:
        from tau_star import Family, solve
        r = solve(Family(n, M)); out['tau_b'] = float(r['tau_b']); out['tau_b_maxatom'] = float(r['max_atom'])
    return out

def planted_layer(st, spec):
    """spec 'X:a:p' -> {B : |B cap X| = p mod 2}, X = first a points;  'R:r:seed' random codim-r coset."""
    n, k = st.n, st.k; allk = ksets(n, k)
    if spec.startswith('X'):
        _, a, p = spec.split(':'); X = (1 << int(a)) - 1
        L = allk[(pc(allk & X) % 2) == int(p)]
    return L

def find_layers(k, T, n, rng, tries=60, r=2):
    """random codim-r cosets (parity checks + targets) whose layer is T-covering."""
    allk = ksets(n, k); allS = ksets(n, n - T); res = []
    for t in range(tries):
        U = [int(rng.integers(1, 1 << n)) for _ in range(r)]; tg = [int(rng.integers(0, 2)) for _ in range(r)]
        ok = np.ones(len(allk), bool)
        for uu, tt in zip(U, tg): ok &= (pc(allk & uu) % 2) == tt
        L = allk[ok]
        if len(L) == 0: continue
        g = np.zeros(1 << n, np.int32); g[L] = 1; g = zeta_sub(g, n)
        if g[allS].min() >= 1: res.append((U, tg, len(L)))
    return res

def run(k, T, n, start, seed, minutes, P=40000, snap_every=60.0, outpath=None):
    rng = np.random.default_rng(seed); import random as _r; prng = _r.Random(seed)
    st = State(k, T, n, prng); c = n - k
    layerF = fwht(np.bincount(ksets(n, k), minlength=1 << n).astype(np.float64))
    if start == 'random' or start == 'complete':
        for B in ksets(n, k): st.add(int(B))
        if start == 'complete':   # complete family on n - s points (K_{k+T}), padded
            keep = (1 << (k + T)) - 1
            for B in list(st.mem):
                if B & ~keep: st.remove(B)
    elif start.startswith('layer'):
        for B in planted_layer(st, start.split('=', 1)[1]): st.add(int(B))
    elif start.startswith('randlayer'):
        r = int(start.split('=')[1]); found = find_layers(k, T, n, rng, tries=200, r=r)
        assert found, 'no covering random layer'
        U, tg, _ = found[0]; allk = ksets(n, k); ok = np.ones(len(allk), bool)
        for uu, tt in zip(U, tg): ok &= (pc(allk & uu) % 2) == tt
        for B in allk[ok]: st.add(int(B))
        start = f'randlayer={r} U={U} t={tg}'
    assert st.covering(), 'start family not T-covering'
    st.reduce_random(); assert st.covering()
    train = Panel(n, c, P, rng); test = Panel(n, c, P, rng)
    N = train.N_of(st.members(), n); cost = float(N.astype(np.float64).prod(1).sum())
    log = dict(k=k, T=T, n=n, start=start, seed=seed, P=P, adm=train.adm, snaps=[])
    def snap(it, temp, acc, full_tau=False):
        Nt = test.N_of(st.members(), n)
        d = dict(it=it, t=round(time.time() - t0, 1), temp=temp, acc=acc, train_cost=cost / train.P * train.adm,
                 **{'test_' + a: b for a, b in test.stats(Nt).items()}, **measures(st, layerF, full_tau))
        log['snaps'].append(d); print(json.dumps(d), flush=True)
        if outpath: json.dump(log, open(outpath, 'w'))
    t0 = time.time(); snap(0, None, None, full_tau=True)
    T0, T1 = 3e-3, 2e-5; it = 0; acc = 0; last = time.time(); dur = minutes * 60
    while time.time() - t0 < dur:
        it += 1; frac = (time.time() - t0) / dur; temp = T0 * (T1 / T0) ** frac
        B = st.mem[prng.randrange(len(st.mem))]
        x = prng.choice([i for i in range(n) if B >> i & 1]); y = prng.choice([i for i in range(n) if not B >> i & 1])
        Bin = B ^ (1 << x) ^ (1 << y)
        if st.inH[Bin]: continue
        st.add(Bin); rem = []
        cand = st.near_members(Bin); prng.shuffle(cand)
        for Bo in cand:
            if st.removable(Bo): st.remove(Bo); rem.append(Bo)
        dN = train.fit(Bin).astype(np.int64)
        for Bo in rem: dN -= train.fit(Bo)
        rows = np.nonzero(dN.any(1))[0]
        old = N[rows].astype(np.float64).prod(1).sum(); Nn = N[rows] + dN[rows]; new = Nn.astype(np.float64).prod(1).sum()
        delta = (new - old) / max(cost, 1.0)
        if delta <= 0 or prng.random() < math.exp(-delta / temp):
            N[rows] = Nn; cost += new - old; acc += 1
        else:
            for Bo in rem: st.add(Bo)
            st.remove(Bin)
        if it % 3000 == 0:   # exact redundancy pass (never increases the objective)
            for Bo in st.mem[:]:
                if st.inH[Bo] and st.removable(Bo):
                    st.remove(Bo)
            train = Panel(n, c, P, rng)   # fresh training panel: limits overfitting to one sample of colourings
            N = train.N_of(st.members(), n); cost = float(N.astype(np.float64).prod(1).sum())
        if time.time() - last > snap_every:
            last = time.time(); snap(it, temp, acc)
    st.reduce_random(); N = train.N_of(st.members(), n); cost = float(N.astype(np.float64).prod(1).sum())
    assert st.covering()
    snap(it, 'final', acc, full_tau=True)
    np.save(outpath.replace('.json', '.npy'), st.members())
    return log

if __name__ == '__main__':
    k, T, n = map(int, sys.argv[1:4]); start = sys.argv[4]; seed = int(sys.argv[5]); minutes = float(sys.argv[6])
    P = int(sys.argv[7]) if len(sys.argv) > 7 else 40000
    tag = start.replace(':', '_').replace('=', '_')
    out = os.path.join(HERE, 'out', f'sa_{k}_{T}_{n}_{tag}_s{seed}.json')
    run(k, T, n, start, seed, minutes, P, snap_every=max(30.0, minutes * 6), outpath=out)
