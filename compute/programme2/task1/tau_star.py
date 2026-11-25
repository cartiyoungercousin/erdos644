r"""PROGRAMME_2 Task 1: tau*_b(H) = min y(V) s.t. y >= 0, y(M) >= 1 for every transversal M of H.
LP over the cut pool + separation oracle (minimum y-weight transversal).  Two oracles:
  * 'bitset' (n <= 25): exact; superset-closure over all 2^n subsets, M is a transversal iff V-M contains no member;
  * 'ilp'    (any n):    HiGHS MILP  min y.z  s.t.  z(B) >= 1 for every member B.
Optional symmetry: y constant on given orbits (orbit-averaging a feasible y keeps feasibility when the family is
invariant, and keeps y(V), so the optimum over orbit-constant y equals tau*_b).
Three stages (cuts are shared):  S1  tau*_b = min y(V);  S2  min max-atom among y with y(V) = tau*_b;
S3  Phi = min over feasible y of y(V) + 7 max y  (Theorem 3 closes H iff Phi < 7/3).
Only exact oracles are used, so the final y is certified feasible up to the 1e-9 tolerance. [computed exact, float LP]"""
import numpy as np, itertools, time
from scipy.optimize import linprog, milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix
from fractions import Fraction

TOL = 1e-9

def popcount(a):
    a = a.astype(np.uint64) if a.dtype != np.uint64 else a
    c = np.zeros(a.shape, np.uint8)
    for s in range(0, 40):
        c += ((a >> np.uint64(s)) & np.uint64(1)).astype(np.uint8)
    return c

class Family:
    def __init__(self, n, masks, name=''):
        self.n = n; self.name = name
        self.masks = np.unique(np.asarray(masks, dtype=np.int64))
        self.full = (1 << n) - 1
        self._cov = None
    def cov(self):
        if self._cov is None:
            n = self.n; cov = np.zeros(1 << n, np.uint8); cov[self.masks] = 1
            for i in range(n):
                v = cov.reshape(-1, 2, 1 << i); v[:, 1, :] |= v[:, 0, :]
            self._trans = (cov[::-1] == 0); self._cov = True
        return self._trans
    def weights(self, y):
        w = np.zeros(1, np.float64)
        for i in range(self.n): w = np.concatenate([w, w + y[i]])
        return w
    def bitset_oracle(self, y, want=150):
        trans = self.cov(); w = self.weights(y); w = np.where(trans, w, np.inf)
        k = min(want, len(w) - 1); idx = np.argpartition(w, k)[:want]
        idx = idx[np.argsort(w[idx])]
        return float(w[idx[0]]), [int(m) for m in idx if w[m] < 1 - TOL]
    def ilp_oracle(self, y, tl=600):
        if not hasattr(self, '_A'):
            rows, cols = [], []
            for v in range(self.n):
                r = np.nonzero((self.masks >> v) & 1)[0]; rows.append(r); cols.append(np.full(len(r), v))
            self._A = csr_matrix((np.ones(sum(len(r) for r in rows)), (np.concatenate(rows), np.concatenate(cols))), shape=(len(self.masks), self.n))
        res = milp(c=np.asarray(y, float), constraints=LinearConstraint(self._A, 1, np.inf), integrality=np.ones(self.n),
                   bounds=Bounds(0, 1), options={'time_limit': tl})
        assert res.status == 0, res.message
        z = np.round(res.x).astype(int); m = sum(1 << v for v in range(self.n) if z[v])
        val = float(np.dot(y, z))
        return val, ([m] if val < 1 - TOL else [])
    def oracle(self, y, kind):
        return self.bitset_oracle(y) if kind == 'bitset' else self.ilp_oracle(y)

def solve(fam, orbits=None, kind=None, verbose=False):
    n = fam.n; kind = kind or ('bitset' if n <= 25 else 'ilp')
    orb = list(range(n)) if orbits is None else list(orbits)
    no = max(orb) + 1; cuts = {}; t0 = time.time(); rounds = 0
    def row_of(m):
        r = [0] * no
        for v in range(n):
            if m >> v & 1: r[orb[v]] += 1
        return tuple(r)
    def lp(stage, tau=None):
        nonlocal rounds
        # variables: u_0..u_{no-1}, t.  atom constraints t >= u_o.
        size = [orb.count(o) for o in range(no)]
        while True:
            A = [[-c for c in r] + [0] for r in cuts]; b = [-1.0] * len(cuts)
            for o in range(no):
                a = [0] * (no + 1); a[o] = 1; a[no] = -1; A.append(a); b.append(0.0)
            if stage == 1: c = size + [0]
            elif stage == 2:
                c = [0] * no + [1]; A.append(size + [0]); b.append(tau + 1e-9)
            else: c = size + [7]
            res = linprog(c, A_ub=np.array(A, float), b_ub=b, bounds=[(0, None)] * (no + 1), method='highs')
            assert res.status == 0, res.message
            u = res.x[:no]; y = [u[orb[v]] for v in range(n)]
            val, viol = fam.oracle(y, kind); rounds += 1
            if verbose: print(f'  stage {stage} round {rounds} obj={res.fun:.6f} minTrans={val:.6f} new={len(viol)} cuts={len(cuts)}', flush=True)
            if not viol: return res.fun, y
            for m in viol: cuts[row_of(m)] = 1
    cuts[row_of(fam.full)] = 1
    tau_b, y1 = lp(1)
    tmax, y2 = lp(2, tau_b)
    phi, y3 = lp(3)
    return dict(tau_b=tau_b, max_atom=tmax, phi=phi, y=y2, y_phi=y3, rounds=rounds, cuts=len(cuts), secs=time.time() - t0, oracle=kind,
                symmetric=orbits is not None)

def min_transversal_size(fam, kind=None):
    kind = kind or ('bitset' if fam.n <= 25 else 'ilp')
    return round(fam.oracle([1.0] * fam.n, kind)[0])

def frac(x):
    f = Fraction(x).limit_denominator(2000)
    return f'{f.numerator}/{f.denominator}' if abs(float(f) - x) < 1e-7 else '-'

SEVEN_THIRDS = 7 / 3
def classify(r):
    # Theorem 3 with the best y: Phi = min (y(V) + 7 max y) < 7/3 ; also with the tau*_b-optimal y of minimal atom
    cond_opt = r['tau_b'] + 7 * r['max_atom'] < SEVEN_THIRDS - 1e-9
    cond_phi = r['phi'] < SEVEN_THIRDS - 1e-9
    return cond_opt, cond_phi

class U1Family:
    """U1 = bulk(G') + {(X-x)+f_x}: 12-uniform on 34 points (old 0..21, fresh f_x = 22+x).  Exact oracle (bitset on the 22 old points):
    a transversal is (M0 on old points, F fresh points); M0 must meet every bulk member; the 11-member X-x is uncovered by M0 iff
    M0&X is empty or {x}; then f_x is needed.  Minimum over M0 of y(M0) + sum of y(f_x) over uncovered x."""
    def __init__(self, G, nx=12, name=''):
        self.n = 22 + nx; self.nx = nx; self.name = name
        Xm = (1 << nx) - 1
        pc = lambda m: bin(m).count('1')
        self.bulk = Family(22, [b for b in G if pc(b) == 12], name + ' bulk')
        short = [b for b in G if pc(b) == 11]
        assert sorted(short) == sorted(Xm & ~(1 << x) for x in range(nx)), 'the 11-members must be exactly X-x'
        self.masks = np.array([b | (1 << (22 + next(x for x in range(nx) if not b >> x & 1))) if pc(b) == 11 else b for b in G], dtype=np.int64)
        self.full = (1 << self.n) - 1
        self.xb = np.arange(1 << 22, dtype=np.int64) & Xm
        self.xpop = popcount(self.xb)
    def oracle(self, y, kind=None, want=150):
        y = np.asarray(y, float); nx = self.nx; yf = y[22:22 + nx]
        trans = self.bulk.cov(); w = self.bulk.weights(y[:22])
        extra = np.zeros(1 << nx)
        extra[0] = yf.sum()
        for x in range(nx): extra[1 << x] = yf[x]
        w = np.where(trans, w + extra[self.xb], np.inf)
        k = want; idx = np.argpartition(w, k)[:want]; idx = idx[np.argsort(w[idx])]
        out = []
        for m in idx:
            if w[m] >= 1 - TOL: break
            m = int(m); xs = m & ((1 << nx) - 1)
            f = 0
            if xs == 0: f = (1 << nx) - 1
            elif xs & (xs - 1) == 0: f = xs
            out.append(m | (f << 22))
        return float(w[idx[0]]), out
    def check_transversal(self, M):
        return bool(np.all((self.masks & M) != 0))
