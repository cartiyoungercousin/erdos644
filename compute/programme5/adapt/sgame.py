"""The S-game ("spectrum game"): adaptive finishing of depth <= 3 from a pair, with global intersection information.

Model (units of k, k -> infinity, grid 1/G for intersection sizes).  The adversary commits to the set S of pair-
intersection sizes of his family (a real family has one; the 6/7 manuscript's Gap(l,u) and "dichotomy" statements are
exactly statements "S misses an interval").  Every response must meet every earlier member in a size from S.
The requester may start from ANY pair with |E cap F| = q in S (it exists in the family).  From it she has at most
three adaptive requests, each depending on all earlier responses, then one static batch (<= 7 members kept):
  round 1  DUMP(u1,u2): E cap F + u1 of E-F + u2 of F-E (u1+u2 = t-q)  -> G with traces y <= 1-q-u1, z <= 1-q-u2,
           y,z in S, y+z >= 3-q-nu (room; nu = n/k);  triple (q,y,z).
  round 2-3 / finish, for the triple, any of
   (a) static: four blocks, all 715 classes (t*_+ table from beat78/tstar.py, zero cells treated as 0+);
   (b) one adaptive request + three static (6/7 manuscript Lemmas 4.1-4.7, normalised; 4.4-4.6 with the best
       Gap(l,u) that S allows, 4.7 with the dichotomy threshold m = max S cap [0,1/2]); all 6 orientations;
   (c) heavy route (Theorem 5.2 branch M <= h, generalised): a cell x = |A cap B| > 1/2; request X+Y+Z + rest of P_C
       -> H; if |C cap H| = b <= 1/2 the triple (A,C,H) or (B,C,H) must close by (a)/(b); if b > 1/2, Lemma 4.8
       (I, then two static requests) with its exact normalised conditions.
Removing q from S is sound once pair q closes against every S-consistent answer; iterate to the greatest fixed
point S*.  She wins iff S* misses [0, 1-t] (a request of t points of any member gives a pair there).
usage: py -3.14 sgame.py G nu t [v]     |  py -3.14 sgame.py G nu scan tlo thi steps"""
import sys, os, itertools, numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
EPS = 1e-9
PERMS = list(itertools.permutations(range(3)))

def load_static(G):
    fn = os.path.join(HERE, 'logs', 't3_%d.npy' % G)
    if not os.path.exists(fn): fn = os.path.join(HERE, '..', 'beat78', 'logs', 't3_%d.npy' % G)
    T3 = np.load(fn)
    return T3

class Game:
    def __init__(self, G, T3):
        self.G = G; self.T3 = T3
        g = np.arange(G + 1) / G; self.g = g
        self.X, self.Y, self.Z = np.meshgrid(g, g, g, indexing='ij')
        self.feas = ~np.isnan(T3)

    def sym(self, A):
        out = np.zeros_like(A)
        for p in PERMS: out |= np.transpose(A, p)
        return out

    def basic(self, S, t, parts=False):
        """closes by (a) static or (b) one adaptive request; boolean over the grid"""
        X, Y, Z, G, g = self.X, self.Y, self.Z, self.G, self.g
        Sm = X + Y + Z
        le = lambda a, b: a <= b + EPS
        stat = np.nan_to_num(self.T3, nan=9) <= t + EPS
        L41 = (le(X + Y, t) & le(1 + 2 * X, 2 * t) & le(1 + 2 * Y, 2 * t) & le(1 + X - Y - Z, t) & le(1 - X + Y - Z, t)
               & le(3 - Sm, 3 * t) & le(3 + Sm, 5 * t) & le(1 + X + Y + 2 * Z, 3 * t) & le(2 + 3 * Z, 4 * t))
        L42 = le(Sm, t) & le(1 + 2 * Y, 2 * t) & le(1 + 2 * X - Y + Z, 2 * t) & le(1 + 2 * X + Y + 3 * Z, 3 * t)
        L43 = le(Sm, t) & le(1 + 3 * X, 3 * t) & le(1 - X + Z, t) & le(1 + 2 * X + 3 * Y + Z, 3 * t)
        D = np.maximum(Sm - t, 0)
        # dichotomy threshold
        low = np.where(S & (g <= 0.5 + EPS))[0]
        m = g[low.max()] if len(low) else 0.0
        L47c = le(Y + Z, t) & le(m + Z, t) & le(X + m, t) & le(1 + Y - Z, t) & le(2 + X - 2 * Z, 2 * t) & le(2 + X + m - Z, 3 * t)
        L47a = le(1 - X + Y + D, t) & le(2 - 2 * X + Z + D, 2 * t) & le(2 - Z + D, 2 * t) & le(3 - X - Y + D, 3 * t)
        L47b = le(Sm, t) & le(1 - X + Y, t) & le(2 - 2 * X + Z, 2 * t)
        L47 = L47c & (L47a | L47b)
        # gap lemmas: for every u, l = max S cap [0,u]
        L44 = np.zeros_like(stat); L45 = np.zeros_like(stat); L46 = np.zeros_like(stat)
        idx = np.where(S)[0]
        for ui in range(G + 1):
            u = g[ui]
            below = idx[idx <= ui]
            l = g[below.max()] if len(below) else 0.0
            p = np.maximum(0, 1 - X - Y - u); tt = np.maximum(0, 1 - X - Z - u)
            L44 |= le(Sm + p + tt, t) & le(1 + 3 * X + p + tt, 3 * t) & le(Y + Z + 2 * l, t)
            L45 |= (le(X + Y, t) & le(1 - X - Y, u) & le(1 - X - Z + D, u) & le(2 * X + 2 * D + 1 - Y - Z, 2 * t)
                    & le(Y + Z + 2 * l, t) & le(2 + X - Y + l + D, 3 * t))
            gg = np.maximum(0, 1 - Y - u)
            L46 |= (le(gg, np.minimum(X, Z)) & le(Y + 2 * gg, t) & le(X + l, t) & le(Z + l, t) & le(1 + 2 * Y, 2 * t)
                    & le(3, 4 * t) & le(3 + Sm, 5 * t))
        lem = {'static': stat, '4.1': self.sym(L41), '4.2': self.sym(L42), '4.3': self.sym(L43), '4.4': self.sym(L44),
               '4.5': self.sym(L45), '4.6': self.sym(L46), '4.7': self.sym(L47)}
        out = np.zeros_like(stat)
        for v in lem.values(): out |= v
        out &= self.feas
        return (out, lem, m) if parts else out

    def heavy(self, S, t, CB, m):
        """(c): heavy route for triples (x,y,z) with x = cell A cap B > 1/2 (axis 0), y = A cap C, z = B cap C."""
        G, g = self.G, self.g
        NB = (~CB) & self.feas & S[None, :, None] & S[None, None, :]   # NB[y, ah, b]: triple (y,ah,b) does not close, ah,b in S
        F1 = np.maximum.accumulate(NB, axis=1)                  # F1[y, A, b] = exists ah <= A with NB
        Sidx = np.where(S)[0]
        def maxS(hi):            # max S cap [0, hi] (grid index), or -1
            c = Sidx[Sidx <= hi]
            return c.max() if len(c) else -1
        H = np.zeros((G + 1,) * 3, bool)
        half = G // 2
        for xi in range(half + 1, G + 1):
            x = g[xi]
            for yi in range(0, G - xi + 1):
                for zi in range(0, G - xi + 1):
                    if not (S[yi] and S[zi]): continue
                    y, z = g[yi], g[zi]
                    if x + y + z > t + EPS: continue
                    bmax = int(np.floor((1 - t + x) * G + EPS))
                    Amax, Bmax = G - xi - yi, G - xi - zi
                    # branch b <= 1/2: needs, for every b in S, the triple (y,ah,b) or (z,bh,b) to close
                    bl = min(half, bmax)
                    okA = True
                    if bl >= 0 and Amax >= 0 and Bmax >= 0:
                        fa = F1[yi, Amax, :bl + 1] & F1[zi, Bmax, :bl + 1] & S[:bl + 1]
                        okA = not fa.any()
                    if not okA: continue
                    # branch b > 1/2
                    hb = Sidx[(Sidx > half) & (Sidx <= bmax)]
                    if len(hb):
                        b = g[hb.max()]
                        ia, ib = maxS(Amax), maxS(Bmax)
                        rho = (g[ia] if ia >= 0 else 0) + (g[ib] if ib >= 0 else 0)
                        sig = y + z
                        mx, mn = max(sig, rho), min(sig, rho)
                        ok = (t - 0.5 - mx >= -EPS) and (2 * x + b + 0.5 + mx <= 3 * t + EPS)
                        if ok and b > t - x + EPS:
                            jI = maxS(int(np.floor((0.5 + mn - sig) * G + EPS)))
                            ok = (jI < 0) or (g[jI] <= t - x + EPS)
                        if not ok: continue
                    H[xi, yi, zi] = True
        return self.sym(H)

    def closes(self, S, t):
        CB, lem, m = self.basic(S, t, parts=True)
        Hv = self.heavy(S, t, CB, m)
        return CB | Hv, lem, Hv

    def pair_closes(self, S, t, nu, CL):
        """for each q in S: is there a DUMP split such that every S-consistent answer gives a closing triple?"""
        G, g = self.G, self.g
        rho_room = nu                       # y+z >= 3-q-nu
        res = np.zeros(G + 1, bool); how = {}
        bad = (~CL) & self.feas & S[None, :, None] & S[None, None, :]     # infeasible answers do not exist
        for qi in range(G):
            if not S[qi]: continue
            q = g[qi]
            if q > t + EPS: continue
            Bq = bad[qi]                                        # Bq[y,z]: answer (y,z) survives
            # DUMP(h1,h2) of BEAT78 §1.3: h_i in [1-t, 1-q], 2-t-q <= h1+h2 <= min(2-2q, 1+rho); answer y <= h1,
            # z <= h2, y+z >= h1+h2-rho (rho = nu-1-t: the rest of her budget goes outside E u F).
            rho = nu - 1 - t
            val = np.where(Bq, g[:, None] + g[None, :], -1e9)
            Mx = np.maximum.accumulate(np.maximum.accumulate(val, 0), 1)   # max y+z of a survivor in the box
            win = None
            for h1 in range(G + 1):
                H1 = g[h1]
                if H1 < 1 - t - EPS or H1 > 1 - q + EPS: continue
                lo2 = max(1 - t, 2 - t - q - H1); hi2 = min(1 - q, 1 + rho - H1)
                if lo2 > hi2 + EPS: continue
                cands = [lo2] + [g[j] for j in range(G + 1) if lo2 < g[j] <= hi2 + EPS]
                for H2 in cands:
                    j2 = int(np.floor(H2 * G + EPS))
                    if Mx[h1, j2] < H1 + H2 - rho - EPS:
                        win = (H1, H2); break
                if win is not None: break
            if win is not None:
                res[qi] = True; how[qi] = win
        return res, how

def solve(G, T3, nu, t, verbose=False, game=None):
    gm = game or Game(G, T3)
    S = np.ones(G + 1, bool); S[G] = False
    it = 0
    while True:
        it += 1
        CL, lem, Hv = gm.closes(S, t)
        rem, how = gm.pair_closes(S, t, nu, CL)
        if verbose:
            print('  iter %d: |S|=%d remove %s' % (it, S.sum(), [i for i in range(G + 1) if rem[i]]), flush=True)
        if not rem.any(): break
        S &= ~rem
    # START(u) (BEAT78 §1.3): u of a member + t-u outside gives a pair in [max(0,1-u-rho), 1-u]; S must meet all.
    rho = nu - 1 - t; g = gm.g
    start_hit = True
    for uu in range(1, G + 1):
        u = g[uu]
        if u > t + EPS: break
        lo, hi = max(0.0, 1 - u - rho), 1 - u
        if not np.any(S & (g >= lo - EPS) & (g <= hi + EPS)):
            start_hit = False; break
    return start_hit, S, (CL, lem, Hv)

def compact(S, G):
    out, i = [], 0
    while i <= G:
        if S[i]:
            j = i
            while j + 1 <= G and S[j + 1]: j += 1
            out.append('%d-%d' % (i, j) if j > i else '%d' % i); i = j + 1
        else: i += 1
    return '[' + ','.join(out) + ']/%d' % G

if __name__ == '__main__':
    G = int(sys.argv[1]); nu = float(sys.argv[2]); T3 = load_static(G)
    gm = Game(G, T3)
    if sys.argv[3] == 'scan':
        tlo, thi, n = float(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6])
        for tt in np.linspace(tlo, thi, n):
            adv, S, _ = solve(G, T3, nu, tt, game=gm)
            print('t=%.5f eps=%.5f  %s  |S*|=%d  S*=%s' % (tt, tt - .75, 'ADVERSARY' if adv else 'requester',
                  S.sum(), compact(S, G)), flush=True)
    else:
        t = float(sys.argv[3])
        adv, S, (CL, lem, Hv) = solve(G, T3, nu, t, verbose=True, game=gm)
        print('ADVERSARY survives' if adv else 'REQUESTER wins')
        print('S* =', S.sum(), compact(S, G))

