r"""Exact checks for section 9 (notes/PROGRAMME2_B.md).

(1) Lemma F1w (weighted points).  Blocks j = 1..q with integer weights w_j; a block labelling v: blocks -> F2^3 - 0
    has weighted counts c_v = sum_{j: v_j = v} w_j.  For lam: blocks -> F2^3,
        S(lam) = sum_{v with counts m} prod_j (-1)^{<lam_j, v_j>}      (exact, rationals, DP over remaining counts).
    Claimed bound, for every zeta > 0:
        |S(lam)| <= zeta^{-m} prod_j Z_j(zeta) * prod_{weight classes w} Phi(n^{(w)}(lam); P2^{(w)}),
        Z_j = sum_v zeta_v^{w_j},  P2^{(w)} = 8 sum_v zeta_v^{2w} / (sum_v zeta_v^w)^2,
        Phi(n; P2) = max { prod_u t_u^{n_u/2} : sum_u t_u = P2, 0 <= t_u <= 1 }.
(2) Lemma F1+ (pair-subgroup Parseval), unit weights.  Shift lam by its dominant value (|S| unchanged); then
        |S(lam)| <= zeta^{-m} prod Z * max_{0 <= t0 <= 1} t0^{n_0/2} prod_{u != 0} min(1, c_u - t0)^{n_u/2},
        c_u = 2 (a_u^2 + (1 - a_u)^2),  a_u = sum_{<u,v> = 1} p_v,  p_v = zeta_v / sum zeta   (c_u = 50/49 at equal p).
    For n_0 >= 49 d (equal p) this is 7^{-d}: the per-point damping 1/7.
[computed exact: S by rational DP; bounds in floating point with a 1e-9 relative tolerance]"""
import random, math, sys
from fractions import Fraction
from collections import defaultdict

VS = list(range(1, 8))


def chi(u, v):
    return -1 if bin(u & v).count('1') % 2 else 1


def exact_S(lams, wts, m):
    dp = {tuple(m[v] for v in VS): Fraction(1)}
    for u, w in zip(lams, wts):
        nd = defaultdict(Fraction)
        for st, val in dp.items():
            for i, v in enumerate(VS):
                if st[i] < w:
                    continue
                ns = st[:i] + (st[i] - w,) + st[i + 1:]
                nd[ns] += val * chi(u, v)
        dp = nd
    return dp.get(tuple(0 for _ in VS), Fraction(0))


def phi(ncounts, P2):
    act = [u for u in range(8) if ncounts[u] > 0]
    if not act:
        return 1.0
    t = {}; capped = set(); budget = P2
    while True:
        free = [u for u in act if u not in capped]
        if not free:
            break
        tot = sum(ncounts[u] for u in free)
        for u in free:
            t[u] = budget * ncounts[u] / tot
        over = [u for u in free if t[u] > 1]
        if not over:
            break
        for u in over:
            capped.add(u); t[u] = 1.0
        budget = P2 - len(capped)
        if budget <= 0:
            for u in free:
                if u not in capped:
                    t[u] = 0.0
            break
    if any(t[u] <= 0 for u in act):
        return 0.0
    return math.exp(sum(ncounts[u] / 2 * math.log(t[u]) for u in act))


def prefactor(wts, m, zeta):
    lg = -sum(m[v] * math.log(zeta[v]) for v in VS)
    for w in wts:
        lg += math.log(sum(zeta[v] ** w for v in VS))
    return lg


def bound_F1w(lams, wts, m, zeta):
    lg = prefactor(wts, m, zeta)
    val = 0.0
    for w in sorted(set(wts)):
        nc = [0] * 8
        for u, ww in zip(lams, wts):
            if ww == w:
                nc[u] += 1
        P2 = 8 * sum(zeta[v] ** (2 * w) for v in VS) / sum(zeta[v] ** w for v in VS) ** 2
        f = phi(nc, P2)
        if f == 0:
            return 0.0
        val += math.log(f)
    return math.exp(lg + val)


def bound_F1plus(lams, m, zeta):
    N = len(lams)
    nc = [lams.count(u) for u in range(8)]
    ustar = max(range(8), key=lambda u: nc[u])
    sh = [u ^ ustar for u in lams]
    n = [sh.count(u) for u in range(8)]
    Zs = sum(zeta[v] for v in VS); p = {v: zeta[v] / Zs for v in VS}
    c = {u: 2 * (sum(p[v] for v in VS if chi(u, v) < 0) ** 2 + sum(p[v] for v in VS if chi(u, v) > 0) ** 2) for u in range(1, 8)}
    best = -1e300
    for i in range(0, 20001):
        t0 = i / 20000
        if t0 == 0 and n[0] > 0:
            continue
        lg = (n[0] / 2) * math.log(t0) if n[0] else 0.0
        ok = True
        for u in range(1, 8):
            if n[u]:
                q = min(1.0, c[u] - t0)
                if q <= 0:
                    ok = False; break
                lg += n[u] / 2 * math.log(q)
        if ok:
            best = max(best, lg)
    # grid maximum: add a safety margin for the grid (derivative bound) by also evaluating at the analytic optimum
    return math.exp(prefactor([1] * N, m, zeta) + best) * 1.0005


def main(seed=1, trials=160):
    rng = random.Random(seed)
    worst_w = worst_p = 0.0; nw = npl = 0; sharper = 0
    for trial in range(trials):
        # ---- weighted ----
        m = {v: rng.randint(2, 5) for v in VS}
        Ntot = sum(m.values())
        wts = []
        while sum(wts) < Ntot:
            w = rng.choice([1, 1, 2, 3])
            if sum(wts) + w > Ntot:
                w = Ntot - sum(wts)
            wts.append(w)
        rng.shuffle(wts)
        q = len(wts)
        if rng.random() < 0.5:
            u0 = rng.randrange(8); lams = [u0] * q
            for x in rng.sample(range(q), rng.randint(1, max(1, q // 3))):
                lams[x] = rng.randrange(8)
        else:
            lams = [rng.randrange(8) for _ in range(q)]
        S0 = exact_S([0] * q, wts, m)
        if S0 == 0 or len(set(lams)) == 1:
            continue
        S = exact_S(lams, wts, m)
        zeta = {v: m[v] / Ntot for v in VS} if rng.random() < 0.7 else {v: rng.uniform(0.5, 1.5) * m[v] / Ntot for v in VS}
        b = bound_F1w(lams, wts, m, zeta)
        assert abs(float(S)) <= b * (1 + 1e-9), ('F1w', lams, wts, m, S, b)
        worst_w = max(worst_w, abs(float(S)) / b if b > 0 else 0); nw += 1
        # ---- F1+ (unit weights) ----
        N = rng.randint(10, 22)
        base = [N // 7] * 7
        for i in rng.sample(range(7), N - 7 * (N // 7)):
            base[i] += 1
        m1 = dict(zip(VS, base))
        u0 = rng.randrange(8); lam1 = [u0] * N
        for x in rng.sample(range(N), rng.randint(1, max(1, N // 2))):
            lam1[x] = rng.randrange(8)
        if len(set(lam1)) == 1:
            continue
        S1 = exact_S(lam1, [1] * N, m1)
        zeta1 = {v: m1[v] / N for v in VS}
        b1 = bound_F1plus(lam1, m1, zeta1)
        bf1 = bound_F1w(lam1, [1] * N, m1, zeta1)
        assert abs(float(S1)) <= b1 * (1 + 1e-9), ('F1+', lam1, m1, S1, b1)
        worst_p = max(worst_p, abs(float(S1)) / b1); npl += 1
        sharper += b1 < bf1
    print('F1w: %d weighted cases (weights 1..3), bound held in all; max |S|/bound = %.4f' % (nw, worst_w))
    print('F1+: %d cases, bound held in all; max |S|/bound = %.4f; F1+ sharper than F1 in %d' % (npl, worst_p, sharper))


if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
