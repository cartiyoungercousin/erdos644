"""Independent check of PETAL Theorem N (section 12).
Part 1: exact rational evaluation of a0, beta, L*(a0,beta), the delta_N table, thresholds 0.7903 / 0.7670.
Part 2: legality of adversary A(t,delta) (colour rule, free mass) over a dense (t,delta) grid.
Part 3: discrete simulation: legal A(t,delta) with proportional own parts, slivers (sliver rule), random leaks,
        random requester (colour forcing, serving random triples).  Every triple-free quadruple must have a
        grid with cells >= (a0,beta) - O(1); also sigma <= k+T (so Theorem K(ii) applies)."""
import sys, random, itertools
from fractions import Fraction as Fr
import numpy as np


def lstar(a, b):
    c = [a + b / 3, b + a / 3, 2 * (a + b) / 3]
    if 2 * b >= a: c.append(3 * a / 4 + b / 2)
    if 2 * a >= b: c.append(3 * b / 4 + a / 2)
    return min(c)


def a0(t, d): return 1 - t / 2 - d
def beta(t, d): return (1 - d) * (2 - 3 * t / 2 - 2 * d) / (2 - t - 2 * d)
def margin(t, d): return lstar(a0(t, d), beta(t, d)) - t


def dN(t):
    if margin(t, Fr(0)) <= 0: return None
    lo, hi = Fr(0), Fr(1, 2)
    for _ in range(80):
        mid = (lo + hi) / 2
        if margin(t, mid) > 0: lo = mid
        else: hi = mid
    return lo


def bis(f, lo, hi):
    for _ in range(80):
        mid = (lo + hi) / 2
        if f(mid): lo = mid
        else: hi = mid
    return lo


def part1():
    print("== Part 1: exact values")
    t = Fr(3, 4); d = Fr(51, 1000)
    print("t=3/4 d=0.051: a0=%s beta=%.5f L*=%.5f margin=%.6f" % (a0(t, d), float(beta(t, d)), float(lstar(a0(t, d), beta(t, d))), float(margin(t, d))))
    for tt in ("0.75", "0.76", "0.77", "0.78", "0.79"):
        t = Fr(tt); x = dN(t)
        print(tt, "delta_N=%.4f" % float(x), " t/26=%.4f" % float(t / 26), " 7/5-17t/10=%.4f" % float(Fr(7, 5) - 17 * t / 10), " (delta<1-t:", x < 1 - t, ")")
    print("sup t with (N) at delta=0: %.5f" % float(bis(lambda t: margin(t, Fr(0)) > 0, Fr(3, 4), Fr(9, 10))))
    print("sup t with delta_N(t)>t/26: %.5f" % float(bis(lambda t: (dN(t) is not None and dN(t) > t / 26), Fr(3, 4), Fr(9, 10))))
    bad = 0
    for ti in range(75, 80):
        t = Fr(ti, 100)
        prev = None
        for di in range(0, 60):
            d = Fr(di, 1000)
            m = margin(t, d)
            if prev is not None and prev <= 0 and m > 0: bad += 1
            prev = m
    print("non-monotone sign changes of margin in delta (t=.75..79):", bad)


def part2():
    print("== Part 2: legality of the colour rule / free mass (continuum)")
    bad = 0; N = 0
    for ti in range(66, 101):
        t = Fr(ti, 100)
        for di in range(0, 400):
            d = Fr(di, 1000)
            if d >= 1 - t: break
            n = 1 + t / 2 - d
            N += 1
            for xi in range(0, 101):
                x = t * Fr(xi, 100)
                for y in (t - x, Fr(0)):
                    if x > t / 2: c = 'F'
                    elif y > t / 2: c = 'A'
                    else: c = 'A'
                    own_s = y if c == 'F' else x; oth_s = x if c == 'F' else y
                    if n - own_s < 1 - d or n - oth_s < d: bad += 1
                    if x <= t / 2 and y <= t / 2:
                        own_s = y; oth_s = x      # colour F
                        if n - own_s < 1 - d or n - oth_s < d: bad += 1
    print("parameter pairs", N, "legality violations", bad)
    t = Fr(3, 4); d = Fr(1, 25)
    print("2(1-d)-n == a0:", 2 * (1 - d) - (1 + t / 2 - d) == a0(t, d), " a0>t/2 iff d<1-t:", (a0(t, d) > t / 2) == (d < 1 - t))
    # t below 2/3: is the 'other arena' mass n-t >= delta guaranteed for all delta<1-t?
    t = Fr(6, 10); d = Fr(39, 100)
    print("t=0.6, d=0.39<1-t: n-t=%s >= d? %s (so legality can fail below t=2/3)" % (float(1 + t / 2 - d - t), (1 + t / 2 - d - t) >= d))


class Game:
    def __init__(self, k, t, delta, rnd, leak_mode):
        self.k = k; self.t = t; self.d = delta; self.rnd = rnd
        self.T = int(t * k); self.dk = int(round(delta * k)); self.own = k - self.dk
        self.n = int(round((1 + t / 2 - delta) * k))
        self.N = 2 * self.n
        self.reg = np.array([0] * self.n + [1] * self.n)
        self.replies = []; self.cols = []
        self.leak_mode = leak_mode
        self.maxsl = 0

    def answer(self, S):
        rnd = self.rnd; k = self.k
        inS = np.zeros(self.N, bool); inS[list(S)] = True
        sA = int(inS[self.reg == 0].sum()); sF = int(inS[self.reg == 1].sum())
        half = self.t * k / 2
        if sA > half: c = 1
        elif sF > half: c = 0
        else: c = rnd.randrange(2)
        free_own = np.where((self.reg == c) & ~inS)[0]
        assert len(free_own) >= self.own, "own arena too small"
        sig = {}
        for p in free_own:
            s = 0
            for j, r in enumerate(self.replies):
                if r[p]: s |= 1 << j
            sig.setdefault(s, []).append(p)
        f = self.own / len(free_own)
        chosen = []; rem = []
        for s, pts in sig.items():
            x = f * len(pts); b = int(x)
            rnd.shuffle(pts)
            chosen += pts[:b]; rem.append((x - b, pts[b:]))
        rem.sort(key=lambda z: -z[0] + rnd.random() * 1e-9)
        need = self.own - len(chosen)
        for fr, pts in rem:
            if need <= 0: break
            if pts: chosen.append(pts[0]); need -= 1
        free_oth = [int(p) for p in np.where((self.reg != c) & ~inS)[0]]
        assert len(free_oth) >= self.dk
        if self.leak_mode == 'reuse' and self.replies:
            sc = {p: sum(1 for r in self.replies if r[p]) for p in free_oth}
            rnd.shuffle(free_oth); free_oth.sort(key=lambda p: -sc[p])
            oth = free_oth[:self.dk]
        else:
            oth = rnd.sample(free_oth, self.dk)
        rep = np.zeros(self.N, bool); rep[chosen] = True; rep[oth] = True
        ns = 0
        for i in range(len(self.replies)):
            for j in range(i + 1, len(self.replies)):
                W = np.where(self.replies[i] & self.replies[j] & ~inS)[0]
                if len(W) and not rep[W].any():
                    rep[rnd.choice(list(W))] = True; ns += 1
        self.maxsl = max(self.maxsl, ns)
        self.replies.append(rep); self.cols.append(c)
        return rep


def quads(reps, new):
    m = len(reps)
    for comb in itertools.combinations(range(m), 4):
        if new not in comb: continue
        R = [reps[i] for i in comb]
        if any((R[a] & R[b] & R[c]).any() for a, b, c in itertools.combinations(range(4), 3)): continue
        yield comb


def part3(k, t, delta, ngames, seed, nreq=9):
    rnd = random.Random(seed)
    a0k = a0(t, delta) * k; bk = beta(t, delta) * k
    nq = 0; viol = 0; maxsl = 0; sig_viol = 0; minL = 9
    for g in range(ngames):
        G = Game(k, t, delta, rnd, rnd.choice(['rand', 'reuse']))
        for step in range(nreq):
            T = G.T; typ = rnd.choice([0, 1, 2, 2, 2, 3])
            S = set()
            if typ == 0:
                S |= set(int(x) for x in rnd.sample(list(np.where(G.reg == 1)[0]), int(T / 2) + 1))
            elif typ == 1:
                S |= set(int(x) for x in rnd.sample(list(np.where(G.reg == 0)[0]), int(T / 2) + 1))
            elif typ == 2 and len(G.replies) >= 3:
                cols = G.cols
                cand = [c for c in itertools.combinations(range(len(G.replies)), 3) if len(set(cols[i] for i in c)) == 2]
                idx = list(rnd.choice(cand)) if cand else rnd.sample(range(len(G.replies)), 3)
                P = set()
                for a, b in itertools.combinations(idx, 2):
                    P |= set(int(x) for x in np.where(G.replies[a] & G.replies[b])[0])
                if len(P) <= T:
                    S |= P
                    room = T - len(P)
                    reg = rnd.randrange(2)
                    pool = [int(p) for p in np.where(G.reg == reg)[0] if int(p) not in S]
                    S |= set(rnd.sample(pool, min(len(pool), rnd.randrange(room + 1))))
            else:
                S |= set(rnd.sample(range(G.N), rnd.randrange(T + 1)))
            S = set(list(S)[:T])
            try:
                G.answer(S)
            except AssertionError:
                break
            for comb in quads(G.replies, len(G.replies) - 1):
                nq += 1
                R = [G.replies[i] for i in comb]
                sigma = 0; grids = []
                for (p, q), (r, s) in (((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))):
                    x = int((R[p] & R[q]).sum()); y = int((R[r] & R[s]).sum())
                    grids.append((x, y)); sigma += x + y
                tol = G.maxsl + 2
                ok = any((x >= a0k - tol and y >= bk - tol) or (y >= a0k - tol and x >= bk - tol) for x, y in grids)
                if not ok:
                    viol += 1
                    print("VIOLATION grids", grids, "a0k=%.1f bk=%.1f" % (a0k, bk))
                if sigma > k + G.T + tol: sig_viol += 1
                minL = min(minL, max(lstar(x / k, y / k) for x, y in grids) - t)
        maxsl = max(maxsl, G.maxsl)
    print("k=%d t=%.3f delta=%.3f: games=%d triple-free quads=%d  grid-claim violations=%d  sigma>k+T violations=%d  max slivers=%d  min over quads (best-grid L* - t)=%.4f"
          % (k, t, delta, ngames, nq, viol, sig_viol, maxsl, minL), flush=True)


if __name__ == "__main__":
    part1(); part2()
    print("== Part 3")
    for (t, d, seed) in ((0.75, 0.04, 1), (0.75, 0.0, 2), (0.76, 0.03, 3), (0.75, 0.05, 4)):
        part3(120, t, d, 200, seed, nreq=11)
