r"""CORE §95-§99: how far up the window can a density / forbidden-configuration argument go?

A *static r-certificate* is r members K_1..K_r (mass c each) plus 7-r requests L_{r+1}..L_7 (mass <= t) such that the
minimal co-types J_x = {i <= r : x in K_i} u {j > r : x in L_j} are nonempty and pairwise intersecting.  By 1.1 and
monotonicity, any T-covering family containing K_1..K_r then has a good seven.  §90 (r = 2), Theorem T and the pencil
(r = 3), Q' (r = 4) are special cases; r = 7 is a good seven among members.

Profile family G(xi, y, w, theta) on V = X u Y u W u R (masses xi, y, w, rest): all c-sets K with K n X = 0, K >= Y,
|K n W| >= theta.  First-order density exponent (nats per k):
    rho = N h(c/N) - max_{p >= theta} [ w h(p/w) + R h((c-y-p)/R) ].
`cert(...)` decides by MILP (scipy/HiGHS) whether some static r-certificate has ALL its r members in G.  If none for
r = 1..7 (with requests allowed mass t + slack), G contains no static certificate, so no theorem of the form
"density >= e^{-rho' k} forces a static certificate" can hold with rho' >= rho.  [computed float]

usage: py -3.14 window_density.py scan  |  py -3.14 window_density.py fw
"""
import itertools, math, sys
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import coo_matrix

SUBS = [J for J in range(1, 128)]
PARTS = 4  # X, Y, W, R


def h(x):
    return 0.0 if x <= 0 or x >= 1 else -x * math.log(x) - (1 - x) * math.log(1 - x)


def cert(N, t, r, xi=0.0, y=0.0, w=0.0, theta=0.0, pair_min=None):
    """True iff a static r-certificate exists with all members in G(xi,y,w,theta).
    pair_min: optionally require |K_i n K_j| >= pair_min for members (pairwise-intersecting family)."""
    c = N - 1
    R = N - xi - y - w
    if R < -1e-12:
        return False
    nz = len(SUBS)
    nv = nz + nz * PARTS
    def mv(Ji, P):
        return nz + Ji * PARTS + P
    rows, lo, hi = [], [], []
    def add(coefs, l, u):
        rows.append(coefs); lo.append(l); hi.append(u)
    idx = {J: i for i, J in enumerate(SUBS)}
    # WLOG the co-type family is a maximal intersecting family: an upset containing exactly one of J, [7]-J.
    for J in SUBS:
        if J != 127 and J < (127 ^ J):
            add({idx[J]: 1, idx[127 ^ J]: 1}, 1, 1)
        for e in range(7):
            if not J >> e & 1:
                add({idx[J]: 1, idx[J | 1 << e]: -1}, -np.inf, 0)
    for i, J in enumerate(SUBS):
        for P in range(PARTS):
            add({mv(i, P): 1, i: -N}, -np.inf, 0)
    vols = [xi, y, w, R]
    for P in range(PARTS):
        add({mv(i, P): 1 for i in range(nz)}, vols[P], vols[P])
    full = (1 << r) - 1
    ub = np.full(nv, np.inf); ub[:nz] = 1
    for i, J in enumerate(SUBS):
        if J & full:
            ub[mv(i, 0)] = 0           # X avoided by every member
        if (J & full) != full:
            ub[mv(i, 1)] = 0           # Y contained in every member
    for m in range(r):
        add({mv(i, P): 1 for i, J in enumerate(SUBS) if J >> m & 1 for P in range(PARTS)}, c, c)
        if w > 0:
            add({mv(i, 2): 1 for i, J in enumerate(SUBS) if J >> m & 1}, theta, np.inf)
    for m in range(r, 7):
        add({mv(i, P): 1 for i, J in enumerate(SUBS) if J >> m & 1 for P in range(PARTS)}, -np.inf, t)
    if pair_min is not None:
        for m1, m2 in itertools.combinations(range(r), 2):
            add({mv(i, P): 1 for i, J in enumerate(SUBS) if (J >> m1 & 1) and (J >> m2 & 1) for P in range(PARTS)},
                pair_min, np.inf)
    ri, ci, vv = [], [], []
    for k, co in enumerate(rows):
        for j, v in co.items():
            ri.append(k); ci.append(j); vv.append(v)
    A = coo_matrix((vv, (ri, ci)), shape=(len(rows), nv))
    integ = np.zeros(nv); integ[:nz] = 1
    res = milp(np.zeros(nv), constraints=LinearConstraint(A.tocsr(), lo, hi), integrality=integ,
               bounds=Bounds(np.zeros(nv), ub), options={'time_limit': 60})
    return res.status == 0


def any_cert(N, t, rs=(3, 4, 5, 6, 7), first=True, **kw):
    out = []
    for r in rs:
        if cert(N, t, r, **kw):
            out.append(r)
            if first:
                return out
    return out


def rho(N, xi, y, w, theta):
    c = N - 1; R = N - xi - y - w
    best = -1e9
    for i in range(401):
        p = theta + (min(w, c - y) - theta) * i / 400
        q = c - y - p
        if p < theta - 1e-12 or q < -1e-12 or q > R + 1e-12:
            continue
        e = (w * h(p / w) if w > 0 else 0) + (R * h(q / R) if R > 0 else 0)
        best = max(best, e)
    return N * h(c / N) - best


def gamma(N, t):
    om = N - 1 - t
    return (N - t) * h(om / (N - t))


def scan():
    t = 0.75 + 1e-4
    tr = t + 2e-3          # robustness: requests may have mass t + 0.002 and still no certificate
    print("t =", t, " certificates tested with request mass", tr)
    for N in [1.76, 1.78, 1.80, 1.85, 1.90, 1.95, 2.00, 2.05, 2.10, 2.15, 2.20, 2.24]:
        c = N - 1; g = gamma(N, t)
        # family A: common core Y; smallest y with no certificate
        lo, hi = 0.0, c
        for _ in range(18):
            mid = (lo + hi) / 2
            if any_cert(N, tr, y=mid): lo = mid
            else: hi = mid
        yA = hi; rA = rho(N, 0, yA, 0, 0)
        # family B: |K n W| >= theta, best over w (pairwise-intersecting threshold family)
        bestB = (9, None)
        for w in np.linspace(0.1, N - 0.05, 24):
            lo, hi = c * w / N, min(w, c)     # theta below typical profile costs nothing; find least safe theta
            if any_cert(N, tr, w=w, theta=hi):
                continue
            for _ in range(14):
                mid = (lo + hi) / 2
                if any_cert(N, tr, w=w, theta=mid): lo = mid
                else: hi = mid
            rB = rho(N, 0, 0, w, hi)
            if rB < bestB[0]: bestB = (rB, (round(w, 3), round(hi, 4)))
        # family C: core y plus threshold on W
        bestC = (9, None)
        for yy in [0.02, 0.05, 0.1, 0.15]:
            for w in np.linspace(0.1, N - yy - 0.05, 12):
                lo, hi = c * w / N, min(w, c - yy)
                if hi <= lo or any_cert(N, tr, y=yy, w=w, theta=hi):
                    continue
                for _ in range(12):
                    mid = (lo + hi) / 2
                    if any_cert(N, tr, y=yy, w=w, theta=mid): lo = mid
                    else: hi = mid
                rC = rho(N, 0, yy, w, hi)
                if rC < bestC[0]: bestC = (rC, (yy, round(w, 3), round(hi, 4)))
        best = min(rA, bestB[0], bestC[0])
        print(f"N={N:.2f} omega={N-1-t:.3f} gamma={g:.4f} | core: y*={yA:.4f} rho={rA:.4f} | "
              f"thresh: rho={bestB[0]:.4f} {bestB[1]} | core+thresh: rho={bestC[0]:.4f} {bestC[1]} | "
              f"min rho - gamma = {best - g:+.4f}", flush=True)


def fw():
    """Frankl-Wilson explicit rate in the strip: |A n B| != l = c - p (p prime, c < 2p) => |A| <= C(n, p-1).
    With l = n - 2T (90.2), p = 2T - k.  Rate (nats per k): N[h(c/N) - h((2t-1)/N)].  Compare with gamma."""
    print("eps   worst N in strip   gamma(N)   FW rate   margin")
    for eps in [0.001, 0.002, 0.005, 0.008, 0.01, 0.012, 0.015, 0.02, 0.03]:
        t = 0.75 + eps
        worst = None
        for i in range(201):
            N = 3 * t - 0.5 + (5 * t - 2 - (3 * t - 0.5)) * i / 200
            c = N - 1; p = 2 * t - 1
            assert c < 2 * p
            m = N * (h(c / N) - h(p / N)) - gamma(N, t)
            if worst is None or m < worst[0]:
                worst = (m, N, gamma(N, t), N * (h(c / N) - h(p / N)))
        print(f"{eps:<6}{worst[1]:<19.4f}{worst[2]:<11.4f}{worst[3]:<10.4f}{worst[0]:+.4f}")


if __name__ == "__main__":
    {"scan": scan, "fw": fw}[sys.argv[1]]()


def scan_xy(Ns, t=0.75 + 1e-4, slack=2e-3, nxi=9):
    """Family G(xi, y): avoid X, contain Y.  For each xi on a grid, least y with no static certificate; report the
    cheapest.  [computed float]"""
    tr = t + slack
    print(f"t = {t}, requests tested at mass t + {slack}", flush=True)
    for N in Ns:
        c = N - 1; g = gamma(N, t); delta = N - 1.75
        best = None
        for xi in np.linspace(0, min(0.6, 1.2 * N - 2.0 + 0.2), nxi):
            if any_cert(N, tr, xi=xi, y=min(c, N - 1.5)): # cannot kill even with y = N - 3/2
                continue
            lo, hi = 0.0, min(c, N - 1.5)
            for _ in range(9):
                mid = (lo + hi) / 2
                if any_cert(N, tr, xi=xi, y=mid): lo = mid
                else: hi = mid
            r_ = rho(N, xi, hi, 0, 0)
            if best is None or r_ < best[0]:
                best = (r_, xi, hi)
        print(f"N={N:.3f} delta={delta:.3f} omega={N-1-t:.4f} gamma={g:.4f}  cheapest (xi, y)=({best[1]:.4f}, {best[2]:.4f})"
              f"  rho={best[0]:.4f}  rho/gamma={best[0]/g:.3f}", flush=True)


def check_threshold(Ns=(1.78, 1.85, 1.95, 2.0, 2.1, 2.2, 2.24), t=0.7521, xi=0.005, d=0.004):
    """MILP check of Theorem 96.1: with xi > 0, certificates exist (r = 4) for y < (delta + 3 eps)/2 and for no r
    when y > (delta + 3 eps)/2.  [computed float]"""
    eps = t - 0.75
    for N in Ns:
        y0 = (N - 1.75 + 3 * eps) / 2
        below = any_cert(N, t, xi=xi, y=y0 - d, first=False)
        above = any_cert(N, t, xi=xi, y=y0 + d, first=False)
        r3 = cert(N, t, 3, xi=xi, y=4 * eps + d)
        print(f"N={N:.2f} y0={y0:.4f}  certs at y0-{d}: {below}   at y0+{d}: {above}   r=3 at y=4eps+{d}: {r3}", flush=True)


def rate_table():
    """rho(G) for G = {K : x0 not in K, K >= Y}, |Y| = (delta + 3 eps)/2 (+), vs gamma.  [computed float]"""
    for eps in [0.0001, 0.001, 0.01, 0.03, 0.05]:
        t = 0.75 + eps
        print(f"eps={eps}:  N  omega  y  rho  gamma  rho/gamma")
        lo, hi = 5 * t - 2, 3 - t
        worst = 0
        for i in range(1, 41):
            N = lo + (hi - lo) * i / 40
            c = N - 1; y = (N - 1.75 + 3 * eps) / 2
            r_ = N * h(c / N) - (N - y) * h((c - y) / (N - y)); g = gamma(N, t)
            worst = max(worst, r_ / g)
            if i in (1, 2, 5, 10, 20, 30, 40):
                print(f"   {N:.4f} {N-1-t:.4f} {y:.4f} {r_:.4f} {g:.4f} {r_/g:.3f}")
        print(f"   max rho/gamma over 40 points of the window: {worst:.3f}")


def scan_thresh(N, t=0.75 + 1e-4, slack=2e-3, ws=8):
    """Families with every point covered (no avoided set): core Y (y = N - 3/2 kills all) and threshold
    families {|K n W| >= theta}.  Least rho with no certificate.  [computed float]"""
    tr = t + slack; c = N - 1; g = gamma(N, t)
    rA = rho(N, 0, N - 1.5, 0, 0)
    best = (rA, 'core y=N-3/2')
    for w in np.linspace(0.15, N - 0.1, ws):
        lo, hi = c * w / N, min(w, c)
        if any_cert(N, tr, w=w, theta=hi):
            continue
        for _ in range(8):
            mid = (lo + hi) / 2
            if any_cert(N, tr, w=w, theta=mid): lo = mid
            else: hi = mid
        rB = rho(N, 0, 0, w, hi)
        if rB < best[0]: best = (rB, f'thresh w={w:.3f} theta={hi:.4f}')
    print(f"N={N:.3f} gamma={g:.4f} core-rho={rA:.4f} best rho={best[0]:.4f} ({best[1]}) best/gamma={best[0]/g:.3f}", flush=True)
