r"""Independent exact tests for Theorem A (RA). Own implementation; nothing imported from the author's code.
Tests:
 T1 Lemma A0 (3-wise intersecting => tau <= (k+1)/2), incl. the |B1 cap B2| >= tau step; tight and adversarial.
 T2 deletion inequality tau(H_A) >= tau(H) - |A|.
 T3 A1 end to end on explicit small families (LP-optimal and perturbed y, many A): colouring, line masses, no L a transversal,
    explicit seven, brute-force absence of a 2-point transversal.
 T4 A2 end to end on actual (implicit-oracle) families with heavy points: Theorem 3H fill with pi=0, then Lemma 2, then brute force.
 T5 known (7,2) families: no branch may apply.
"""
import itertools, random, sys
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog

LINES = [(0,1,3),(1,2,4),(2,3,5),(3,4,6),(4,5,0),(5,6,1),(6,0,2)]
PAIRS = [(1,3),(4,5),(6,2)]          # lines through 0 are {0}+pair
LINES_NO0 = [(a, b, c) for a in PAIRS[0] for b in PAIRS[1] for c in PAIRS[2]]
# check: the 4 lines avoiding 0 are exactly those in LINES not containing 0, each transversal to the 3 pairs
_no0 = {frozenset(l) for l in LINES if 0 not in l}
assert len(_no0) == 4 and all(frozenset(t) in {frozenset(x) for x in LINES_NO0} for t in _no0)
assert all(frozenset((0,)+p) in {frozenset(l) for l in LINES} for p in PAIRS)

# ---------- generic explicit-family tools ----------
def tau(H, n):
    masks = [sum(1 << v for v in B) for B in H]
    for t in range(0, n + 1):
        for T in itertools.combinations(range(n), t):
            m = sum(1 << v for v in T)
            if all(m & b for b in masks): return t
    return None

def good_seven_no2(seven, n):
    """True iff no 2-point (or 1-point) set hits all of the (<=7) members."""
    ms = [set(B) for B in seven]
    pts = range(n)
    for x in pts:
        if all(x in B for B in ms): return False
    for x, y in itertools.combinations(pts, 2):
        if all(x in B or y in B for B in ms): return False
    return True

def color_seven(find, V, col, check_mass=None):
    """Given colouring col: V->0..6, return members B_l inside R_l (or None if some L_l is a transversal)."""
    seven = []
    for ln in LINES:
        L = {v for v in V if col[v] in ln}
        R = set(V) - L
        B = find(R)
        if B is None: return None
        seven.append(B)
    return seven

# ---------- T1 / T2 ----------
def rand_3wise(n, k, rng, tries=400):
    H = []
    for _ in range(tries):
        s = rng.randint(1, k); B = frozenset(rng.sample(range(n), s))
        ok = True
        cand = H + [B]
        for t in itertools.combinations_with_replacement(range(len(cand)), 3):
            if len(t) and len(set(t)) and (len(set(t)) == 0): pass
            if t[0] != len(cand)-1 and t[1] != len(cand)-1 and t[2] != len(cand)-1: continue
            if not (cand[t[0]] & cand[t[1]] & cand[t[2]]): ok = False; break
        if ok: H.append(B)
    return H

def T1(seed, iters):
    rng = random.Random(seed); worst = 0; cnt = 0
    for _ in range(iters):
        n = rng.randint(4, 11); k = rng.randint(2, n)
        H = rand_3wise(n, k, rng, 60)
        if not H: continue
        kk = max(len(B) for B in H)  # k only needs to bound sizes; use stated k too
        t = tau(H, n)
        assert t <= (k + 1) / 2, (H, k, t)
        # proof step: |B1 cap B2| >= tau for all pairs
        for B1 in H:
            for B2 in H: assert len(B1 & B2) >= t
        worst = max(worst, t - (k + 1) / 2); cnt += 1
    # tight: K_n^(k), n = floor((3k-1)/2)
    for k in range(2, 9):
        n = (3 * k - 1) // 2
        H = [frozenset(c) for c in itertools.combinations(range(n), k)]
        assert all(a & b & c for a, b, c in itertools.combinations_with_replacement(H, 3)) if len(H) < 40 else True
        assert tau(H, n) == n - k + 1 <= (k + 1) / 2
    return cnt, worst

def T2(seed, iters):
    rng = random.Random(seed)
    for _ in range(iters):
        n = rng.randint(5, 10); H = [frozenset(rng.sample(range(n), rng.randint(1, 5))) for _ in range(rng.randint(2, 14))]
        A = set(rng.sample(range(n), rng.randint(0, 3)))
        HA = [B for B in H if not (B & A)]
        tH = tau(H, n); tA = tau(HA, n) if HA else 0
        assert tA >= tH - len(A), (H, A)
    return iters

# ---------- LP y for explicit families ----------
def transversal_masks(H, n):
    ms = [sum(1 << v for v in B) for B in H]
    return [m for m in range(1 << n) if all(m & b for b in ms)]

def opt_y(H, n, D=3000):
    tr = transversal_masks(H, n)
    # only minimal ones needed but all is fine for n<=12
    A_ub = -np.array([[1.0 if (m >> v) & 1 else 0.0 for v in range(n)] for m in tr]); b_ub = -np.ones(len(tr))
    res = linprog(np.ones(n), A_ub=A_ub, b_ub=b_ub, bounds=[(0, None)] * n, method='highs')
    y = [F(int(np.ceil(res.x[v] * D - 1e-9)), D) for v in range(n)]
    for m in tr: assert sum(y[v] for v in range(n) if (m >> v) & 1) >= 1
    return y, tr

def check_feasible(y, tr, n):
    return all(sum(y[v] for v in range(n) if (m >> v) & 1) >= 1 for m in tr)

# ---------- A1 (explicit) ----------
def greedy_split(items, y):
    a, b = [], []; ma = mb = F(0)
    for v in sorted(items, key=lambda v: -y[v]):
        if ma <= mb: a.append(v); ma += y[v]
        else: b.append(v); mb += y[v]
    return a, b, ma, mb

def A1_construct(H, n, y, A, triple):
    """triple: <=3 members of H_A (list of sets, len 3 with repeats) with empty common intersection."""
    V = sorted(set().union(*H)); light = [v for v in V if v not in A]
    Lam = sum((y[v] for v in light), F(0)); ap = max((y[v] for v in light), default=F(0))
    col = {v: 0 for v in A}
    cls = [[], [], []]
    for v in light:
        for s in range(3):
            if v not in triple[s]: cls[s].append(v); break
        else: raise AssertionError('triple not empty-intersection')
    for s in range(3):
        a, b, ma, mb = greedy_split(cls[s], y)
        assert abs(ma - mb) <= ap
        for v in a: col[v] = PAIRS[s][0]
        for v in b: col[v] = PAIRS[s][1]
    masses = [sum((y[v] for v in V if col[v] in ln), F(0)) for ln in LINES]
    return col, masses, Lam, ap, V

def T3(seed, iters):
    rng = random.Random(seed); applied = 0; skipped_noA1 = 0
    for it in range(iters):
        n = rng.randint(7, 11)
        mode = rng.choice(['rand', 'rand', 'pendant', 'star', 'comp'])
        if mode == 'rand':
            H = [frozenset(rng.sample(range(n), rng.randint(1, min(6, n - 1)))) for _ in range(rng.randint(3, 16))]
        elif mode == 'pendant':   # H1 + {{b}}
            H = [frozenset(rng.sample(range(n - 1), rng.randint(2, 5))) for _ in range(rng.randint(3, 12))] + [frozenset([n - 1])]
        elif mode == 'star':      # H1 U star_b: members containing b
            H = [frozenset(rng.sample(range(n - 1), rng.randint(2, 5))) for _ in range(rng.randint(3, 10))]
            H += [frozenset(rng.sample(range(n - 1), rng.randint(1, 3))) | {n - 1} for _ in range(rng.randint(1, 8))]
        else:                     # complements of small sets (dense)
            H = []
            for _ in range(rng.randint(4, 14)):
                S = set(rng.sample(range(n), rng.randint(1, 3))); H.append(frozenset(set(range(n)) - S))
        H = list({B for B in H if B})
        V = sorted(set().union(*H))
        # relabel to 0..n-1 contiguous
        mp = {v: i for i, v in enumerate(V)}; H = [frozenset(mp[v] for v in B) for B in H]; n = len(V)
        y, tr = opt_y(H, n)
        for variant in range(3):
            yy = list(y)
            if variant == 1:  # inflate random points (still feasible), creates heavy atoms
                for v in rng.sample(range(n), rng.randint(1, 2)): yy[v] += F(rng.randint(0, 50), 100)
            if variant == 2:  # tiny extra on all
                yy = [a + F(rng.randint(0, 3), 200) for a in yy]
            assert check_feasible(yy, tr, n)
            for th in [F(1, 100), F(1, 10), F(1, 4), F(1, 2), F(11, 10)]:
                A = {v for v in range(n) if yy[v] >= th}
                HA = [B for B in H if not (B & A)]
                trip = None
                for t in itertools.combinations_with_replacement(range(len(HA)), 3):
                    if not (HA[t[0]] & HA[t[1]] & HA[t[2]]): trip = [HA[i] for i in t]; break
                if trip is None: continue
                light = [v for v in range(n) if v not in A]
                Lam = sum((yy[v] for v in light), F(0)); ap = max((yy[v] for v in light), default=F(0))
                if Lam + 3 * ap >= 2: skipped_noA1 += 1; continue
                col, masses, Lam, ap, V2 = A1_construct(H, n, yy, A, trip)
                assert max(masses[i] for i, l in enumerate(LINES) if 0 not in l) <= (Lam + 3 * ap) / 2 < 1
                # exact: no L is a transversal, seven good
                def find(R):
                    for B in H:
                        if B <= R: return B
                    return None
                seven = color_seven(find, V2, col)
                assert seven is not None, ('A1 FAILED: L transversal', H, yy, A)
                assert good_seven_no2(seven, n), ('seven has 2-transversal', H, yy, A)
                applied += 1
    return applied, skipped_noA1

REASON = {}
# ---------- implicit-oracle families (large k) ----------
class Fam:
    """V = A + light. kind 'pool' (all k-subsets), 'cap' (k-subsets with <= c points of A), 'req' (k-subsets with >= e points of A)."""
    def __init__(self, kind, nl, a0, k, par=0):
        self.kind, self.k, self.par = kind, k, par
        self.A = set(range(a0)); self.light = set(range(a0, a0 + nl)); self.V = set(range(a0 + nl)); self.n = a0 + nl
    def find(self, R):
        R = set(R); k = self.k; RA = sorted(R & self.A); RL = sorted(R - self.A)
        if self.kind == 'pool':
            return frozenset((RA + RL)[:k]) if len(R) >= k else None
        if self.kind == 'cap':
            a = min(self.par, len(RA))
            if len(RL) < k - a: return None
            return frozenset(RA[:a] + RL[:k - a])
        if self.kind == 'req':
            e = self.par
            if len(RA) < e or len(R) < k: return None
            S = RA[:e]; rest = [v for v in RA[e:] + RL]
            return frozenset(S + rest[:k - e])
    def min_transversal(self, y):
        """exact min y-weight transversal"""
        k = self.k; n = self.n; ls = sorted(y[v] for v in self.light); nl = len(ls)
        pre = [F(0)]
        for w in ls: pre.append(pre[-1] + w)
        best = None
        A = sorted(self.A)
        for r in range(len(A) + 1):
            for TA in itertools.combinations(A, r):
                wa = sum((y[v] for v in TA), F(0)); ra = len(A) - r
                if self.kind == 'pool': need = max(0, n - r - k + 1)
                elif self.kind == 'cap':
                    a = min(self.par, ra); need = max(0, nl - (k - a - 1))
                else:
                    need = 0 if ra < self.par else max(0, n - r - k + 1)
                if need > nl: continue
                w = wa + pre[need]
                if best is None or w < best: best = w
        return best

def fill_3H(y, light, c):
    """Sequential fill of light points into classes 0..6 until load >= c_p; return class dict."""
    col = {}; p = 0; load = F(0)
    for v in sorted(light, key=lambda v: v):
        while p < 6 and load >= c[p]:
            p += 1; load = F(0)
        col[v] = p; load += y[v]
    return col

def T4(seed, iters):
    rng = random.Random(seed); done = {'A2': 0, 'A1': 0}; skipped = 0
    for it in range(iters):
        kind = rng.choice(['pool', 'cap', 'req', 'pool'])
        k = rng.randint(40, 140); a0 = rng.randint(0, 5)
        par = 0
        if kind == 'cap': par = rng.randint(1, max(1, a0)) if a0 else 1
        if kind == 'req':
            if a0 == 0: continue
            par = rng.randint(1, a0)
        nl = max(1, 2 * k - 1 - a0 + rng.randint(-int(0.25*k), 3)) if rng.random() < 0.8 else rng.randint(max(1, k), 2 * k)
        fam = Fam(kind, nl, a0, k, par)
        # choose y: heavy weight h on A, light weights as small as feasibility allows (scan uniform w by binary search)
        h = F(rng.randint(5, 30), 100) if a0 else F(0)
        if kind == 'req': h = max(h, F(1, a0 - par + 1))
        lo, hi = F(0), F(1)
        for _ in range(40):
            mid = (lo + hi) / 2
            y = {v: h for v in fam.A}; y.update({v: mid for v in fam.light})
            m = fam.min_transversal(y)
            if m is not None and m >= 1: hi = mid
            else: lo = mid
        w = hi
        y = {v: h for v in fam.A}; y.update({v: w for v in fam.light})
        # tiny noise on light weights (keep feasible: only round up)
        for v in fam.light:
            if rng.random() < 0.5: y[v] = w * (1 + F(rng.randint(0, 3), 100))
        mt = fam.min_transversal(y)
        if mt is None or mt < 1:
            print("infeasible case", kind, k, a0, par, nl, mt, float(w)); skipped += 1; continue
        A = set(fam.A); light = sorted(fam.light)
        Lam = sum((y[v] for v in light), F(0)); ap = max(y[v] for v in light)
        yV = sum(y.values(), F(0))
        if not (yV + 7 * ap < F(7, 3)): skipped += 1; REASON[(kind,'room')]=REASON.get((kind,'room'),0)+1; continue
        if Lam + 3 * ap >= 2:
            # ----- A2 branch -----
            sig = min((F(7, 3) - yV - 7 * ap) / 8, (1 - 3 * ap) / 6)
            s = (1 - 3 * ap) / 3 - sig; t = Lam - 6 * s
            assert t >= 3 * ap + 6 * sig >= 0 and s > 0
            c = [t] + [s] * 6; assert sum(c) == Lam
            col = fill_3H(y, light, c)
            for v in A: col[v] = 0
            masses = [sum((y[v] for v in fam.V if col[v] in ln), F(0)) for ln in LINES]
            assert max(masses) < 1, ('A2 mass', [float(m) for m in masses])
            find = fam.find
            seven = color_seven(find, fam.V, col)
            assert seven is not None, 'A2: some L transversal'
            for B in seven: assert len(B) <= k and B
            assert good_seven_no2(seven, fam.n)
            done['A2'] += 1; done['A2_heavy'] = done.get('A2_heavy', 0) + (a0 > 0); done['A2_t0'] = done.get('A2_t0', 0) + (t == 0)
        else:
            # ----- A1 branch: triple in H_A -----
            Vl = set(light); P = [set(), set(), set()]
            for i, v in enumerate(light): P[i % 3].add(v)
            trip = [fam.find(Vl - P[i]) for i in range(3)]
            if any(b is None for b in trip): skipped += 1; continue
            assert not (trip[0] & trip[1] & trip[2]) and all(not (b & A) for b in trip)
            H_dummy = None
            col, masses, Lam2, ap2, V2 = A1_construct([frozenset(fam.V)], fam.n, y, A, trip)
            assert max(masses[i] for i, l in enumerate(LINES) if 0 not in l) < 1
            seven = color_seven(fam.find, fam.V, col)
            assert seven is not None, 'A1: some L transversal'
            assert good_seven_no2(seven, fam.n)
            done['A1'] += 1
    return done, skipped

# ---------- T5: known (7,2) families ----------
def T5():
    out = []
    fams = {}
    fams['K10_6'] = (10, [frozenset(c) for c in itertools.combinations(range(10), 6)])
    n = 8
    star = [frozenset([0]) | frozenset(c) for c in itertools.combinations(range(1, 9), 6)] if False else None
    # star_a(U) + complements of singletons in [8]: points a=0, U=1..?  use the 7-uniform (7,2) family on points {0}+U(size 9) with the 8 co-singletons on [8]=1..8
    U = list(range(1, 10))
    H = [frozenset([0]) | frozenset(c) for c in itertools.combinations(U, 6)]  # contains a
    H += [frozenset(range(1, 9)) - {i} for i in range(1, 9)]                    # complements of singletons in [8], size 7
    fams['star+comp'] = (10, H)
    for name, (n, H) in fams.items():
        V = sorted(set().union(*H)); mp = {v: i for i, v in enumerate(V)}; H = [frozenset(mp[v] for v in B) for B in H]; n = len(V)
        y, tr = opt_y(H, n)
        hit = 0
        for yy in [y] + [[a + F(rng_i, 40) for a in y] for rng_i in (1, 3)]:
            for th in [F(1, 100), F(1, 10), F(1, 4), F(1, 2)]:
                A = {v for v in range(n) if yy[v] >= th}
                HA = [B for B in H if not (B & A)]
                light = [v for v in range(n) if v not in A]
                Lam = sum((yy[v] for v in light), F(0)); ap = max((yy[v] for v in light), default=F(0))
                trip = None
                for t in itertools.combinations_with_replacement(range(len(HA)), 3):
                    if not (HA[t[0]] & HA[t[1]] & HA[t[2]]): trip = [HA[i] for i in t]; break
                a1 = trip is not None and Lam + 3 * ap < 2
                a2 = Lam + 3 * ap >= 2 and sum(yy) + 7 * ap < F(7, 3)
                hit += a1 or a2
        out.append((name, 'tau', tau(H, n), 'tau*_b', float(sum(y)), 'branches applicable', hit))
        assert hit == 0, name
    return out

if __name__ == '__main__':
    s = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    print('T1', T1(s, 300)); print('T2', T2(s, 1500)); print('T3', T3(s, 120)); print('T4', T4(s, int(sys.argv[2]) if len(sys.argv)>2 else 120), REASON); print('T5', T5())
