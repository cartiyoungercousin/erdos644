"""TWIN checks (exact, integer).  py checks.py
 1. nerve formula for D  vs brute-force 2-cover of 7 edges        (random small set systems)
 2. round-6 closed form  vs brute-force min-max in the unit model with free slivers
 3. the 5-state reached in the two-cluster line at t=4/5 (units of 1/5) is lost by the requester
 4. Theorem 8 (FRESH_C) counting inequality on a discrete instance grid
"""
import itertools, random
from fractions import Fraction as F

def downclose(types, n):
    N = set()
    for J in types:
        s = J
        while True:
            N.add(s)
            if s == 0: break
            s = (s - 1) & J
    return N

# ---------- 1 ----------
def check1(trials=3000, seed=1):
    rnd = random.Random(seed); full = 63
    for _ in range(trials):
        n = rnd.randint(4, 9); ksz = rnd.randint(1, min(4, n))
        E = [frozenset(rnd.sample(range(n), ksz)) for _ in range(7)]
        typ = {p: sum(1 << i for i in range(6) if p in E[i]) for p in range(n)}
        realized = {t for t in typ.values() if t}
        nerve = downclose(realized, 6)
        D = {p for p in range(n) if (full ^ typ[p]) in nerve and not (typ[p] == 0)}
        if full in nerve: D = set(range(n))          # type [6] realized: every point of A_7 is dangerous
        pred = bool(E[6] & D)
        pts = range(n)
        brute = any(all((x in e) or (y in e) for e in E) for x in pts for y in pts)
        assert pred == brute, (E, D)
    return trials

# ---------- 2 ----------
def round6_formula(m, nerve, q, T):
    """m: dict type(mask over 5 bits)->units>0 ; nerve: down-closed set of masks (realized incl. slivers)."""
    full = 31; heavy = list(m)
    W = [J for J in heavy if (full ^ J) in nerve]
    nb = {J: [K for K in heavy if (J | K) == full] for J in W}
    best = None
    for k in range(len(W) + 1):
        for B in itertools.combinations(W, k):
            mb = sum(m[J] for J in B)
            if mb > T: continue
            Bs = set(B)
            Wp = [J for J in W if any(K not in Bs for K in nb[J])]
            Wps = set(Wp)
            rest = sum(m[J] for J in W if J not in Wps and J not in Bs)
            val = sum(m[J] for J in Wp) + min(q, max(0, rest - (T - mb)))
            if best is None or val < best: best = val
    return best

def round6_brute(m, nerve, q, T):
    full = 63; heavy = list(m)
    def dists(caps, tot):
        if not caps:
            if tot == 0: yield ()
            return
        for a in range(min(caps[0], tot) + 1):
            for r in dists(caps[1:], tot - a): yield (a,) + r
    caps = [m[J] for J in heavy]; totm = sum(caps); best = None
    for s in dists(caps, min(T, totm)):
        rem = [c - a for c, a in zip(caps, s)]
        newn = set(nerve) | {32}
        for J, r_ in zip(heavy, rem):
            if r_ > 0: newn |= downclose([J | 32], 6)       # free sliver of every unblocked heavy type
        worst = 0
        for j in range(0, q + 1):
            for y in dists(rem, j):
                d = 0
                for J, c, yy in zip(heavy, caps, y):
                    if (full ^ J) in newn: d += c - yy
                    if (full ^ (J | 32)) in newn: d += yy
                worst = max(worst, d)
        if best is None or worst < best: best = worst
    return best

def check2(trials=400, seed=2):
    rnd = random.Random(seed)
    for _ in range(trials):
        q = rnd.randint(2, 3); T = rnd.randint(1, q)
        ntyp = rnd.randint(2, 6)
        types = rnd.sample(range(1, 31), ntyp)
        m = {J: rnd.randint(1, 2) for J in types}
        extra = rnd.sample(range(1, 31), rnd.randint(0, 4))      # zero-mass realized types (old slivers)
        nerve = downclose(list(m) + extra, 5)
        a, b = round6_formula(m, nerve, q, T), round6_brute(m, nerve, q, T)
        assert a == b, (m, extra, q, T, a, b)
    return trials

# ---------- 3 ----------
def check3():
    b = lambda *e: sum(1 << (i - 1) for i in e)
    q, T = 5, 4
    out = {}
    # (a) requester blocked 24 at round 5: 135 heavy
    m = {b(1,3,5): 3, b(2,4): 4, b(1): 2, b(3): 2, b(2): 1, b(4): 1, b(5): 2}
    nerve = downclose([b(1,3,5), b(1,2), b(1,4), b(2,3), b(3,4), b(2,4), b(2,5), b(4,5)], 5)
    out['block24'] = round6_formula(m, nerve, q, T)
    # (b) requester blocked 13 at round 5: 245 heavy (3), 24 keeps 1, 13 = 3
    m = {b(2,4,5): 3, b(2,4): 1, b(1,3): 3, b(1): 2, b(3): 2, b(2): 1, b(4): 1, b(5): 2}
    nerve = downclose([b(2,4,5), b(1,3), b(1,2), b(1,4), b(2,3), b(3,4), b(1,5), b(3,5)], 5)
    out['block13'] = round6_formula(m, nerve, q, T)
    return out, T

# ---------- 4 ----------
def check4():
    bad = []
    for k in range(4, 61):
        for T in range(1, k):
            if 5 * T < 4 * k:
                # need: every (eX,eY) with eX*eY >= T*k - T*T has eX+eY > T  (eX<=T, eY<=k)
                need = T * k - T * T
                ok = all(ex + ey > T for ex in range(0, T + 1) for ey in range(0, k + 1) if ex * ey >= need)
                if not ok: bad.append((k, T))
    return bad

if __name__ == '__main__':
    print('check1 (D formula vs brute 2-cover): ok on', check1(), 'random 7-tuples')
    print('check2 (round-6 closed form vs brute min-max): ok on', check2(), 'random 5-states')
    o, T = check3(); print('check3 two-cluster 5-states at t=4/5: min mass(D) units =', o, ' T =', T)
    print('check4 Theorem-8 inequality failures for 4<=k<=60, 5T<4k:', check4())
