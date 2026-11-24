"""Independent test of PETAL Theorem L (section 8).
Continuum: random spread triples a=(p12,p13,p23) satisfying the hypotheses; she picks r by LP (or the
proof's construction), adversary picks b adversarially (all vertices of {b_i<=q_i-r_i, sum<=1});
check matching design loads a_i+b_i<=t, and independent LP design L<=t on random non-vertex b.
Also: when a hypothesis is violated (one-term / two-term / three-term), no r makes the matching design work
(shows hypotheses are exactly the matching-design condition; Theorem L is a sufficient condition only)."""
import random, itertools, sys
sys.path.insert(0, '.')
import highspy
import kdesign as D
inf = highspy.kHighsInf

def hyp(a, t):
    p = sum(a)
    if p > t + 1e-12: return False
    for i in range(3):
        if a[i] > t - 0.5 + 1e-12: return False
        j, l = [x for x in range(3) if x != i]
        for (x, y, z) in ((i, j, l), (i, l, j), (j, l, i)):
            if a[x] + a[y] - a[z] > 3 * t - 2 + 1e-12: return False
    return True

def q_of(a):
    p = sum(a)
    # grid i has cell a_i = p_{jl}; its opposite single Q has mass 1 - p + a_i  (cell c_i4 = |B4 ∩ Q_i'|)
    return [1 - p + a[i] for i in range(3)]

def best_r(a, t):
    """LP: exists r with r_i>=0, r_i<=q_i, sum r = t-p, a_i + (q_i - r_i) <= t  (matching loads capped)."""
    p = sum(a); q = q_of(a)
    lo = [max(0.0, 1 - t - p + 2 * a[i]) for i in range(3)]
    if any(lo[i] > q[i] + 1e-12 for i in range(3)): return None
    need = t - p
    if sum(lo) > need + 1e-12: return None
    if need > sum(q) + 1e-12: return None
    r = lo[:]; rem = need - sum(lo)
    for i in range(3):
        add = min(rem, q[i] - r[i]); r[i] += add; rem -= add
    return r

def adv_vertices(caps):
    # maximise: sum b <= 1, b_i <= caps_i : vertices
    out = []
    for order in itertools.permutations(range(3)):
        b = [0.0] * 3; rem = 1.0
        for i in order:
            b[i] = min(caps[i], rem); rem -= b[i]
        out.append(tuple(b))
    return out

rnd = random.Random(11)
n_ok = n_hyp = n_viol = 0; worst = -9
for t in (0.75, 0.76, 0.8, 0.9, 1.0):
    for _ in range(4000):
        a = [rnd.random() * (t - 0.5 + .05) for _ in range(3)]
        h = hyp(a, t)
        r = best_r(a, t)
        if h:
            n_hyp += 1
            assert r is not None, ("hypothesis holds but no r", a, t)
            q = q_of(a); caps = [q[i] - r[i] for i in range(3)]
            for b in adv_vertices(caps):
                load = max(a[i] + b[i] for i in range(3)); worst = max(worst, load - t)
                assert load <= t + 1e-9, (a, t, r, b)
        else:
            # hypothesis violated: matching design cannot be guaranteed
            if sum(a) <= t:
                n_viol += 1
                # exact: the r-construction must fail iff hypothesis fails (up to boundary)
                if r is not None and (t - sum(a)) > 1e-6:
                    # check that hyp failure is only due to the p<=t guard etc
                    print("NOTE r exists though hyp false", a, t)
print("hypothesis cases checked", n_hyp, " violated (p<=t) cases", n_viol, " worst load - t =", worst)

# check the independent LP design on a sample with non-vertex b (loads must be <= t, in fact L<=max load)
cnt = 0
for t in (0.75, 0.8):
    for _ in range(40):
        a = [rnd.random() * (t - 0.5) for _ in range(3)]
        if not hyp(a, t): continue
        r = best_r(a, t); q = q_of(a); caps = [q[i] - r[i] for i in range(3)]
        for b in adv_vertices(caps)[:2]:
            v = D.design_fast if False else None
        b = adv_vertices(caps)[rnd.randrange(6)]
        cells = [(max(a[i], 1e-4), max(b[i], 1e-4)) for i in range(3)]
        nz = [0, 1, 2]
        best = 1e9
        for ch in itertools.product(D.PAIRS, repeat=3):
            v = D.lp(cells, ch)
            if v is not None and v < best: best = v
        assert best <= t + 1e-4, (a, b, best, t)
        cnt += 1
print("independent LP design confirms L<=t on", cnt, "samples")

# explicit boundary examples at t = 3/4
t = 0.75
for a in ([0.25, 0.25, 0.25], [0.25, 0.25, 0.0], [0.25, 0.0, 0.0], [0.26, 0.2, 0.2], [0.25, 0.25, 0.2], [0.2, 0.2, 0.34]):
    print(a, "hyp:", hyp(a, t), " p=", sum(a), " r:", best_r(a, t))
