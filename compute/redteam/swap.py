r"""RED TEAM §12: the twin's SWAP adversary (TWIN 18.6 F1/F2) against the free 8-request requester.

Adversary on N points (units of k), deterministic:
  replies 2..(w-1) before the swap round w: at replies 2 and 3 he OMITS unused (pool) points first (vertex rule,
      order pool, then lowest degree); any further pre-swap rounds (F2) are proportional;
  reply w (the swap): take every unrequested unused point first, then every unrequested point lying only in B_1,
      then the rest proportionally (same fraction of every other unrequested class);
  afterwards proportional.
Requester: free (any requests, any discard), full budget in the MILP.  The swap round is bilinear in
q = (unrequested pool) + (unrequested B_1-only); the MILP fixes q = q0 (a RESTRICTION ON HER, so every line found is a
legal line; the adversary is never favoured) and q0 is scanned.  Winning lines are replayed with the true rule in
exact rational arithmetic (`exact_run`, rule applied with the true unrequested masses, any q) at T = budget + margin.
"""
import pulp, sys, time, json
from fractions import Fraction as Fr
def popc(x): return bin(x).count("1")
LOW = lambda ty: sorted(ty, key=lambda J: (popc(J), J))

def solve(T, N, w, q0, drop, tl=120, msg=False):
    E = 7
    prob = pulp.LpProblem("swap", pulp.LpMinimize); cnt = [0]
    def V(lo=0, hi=None, cat="Continuous"):
        cnt[0] += 1; return prob.add_variable(f"v{cnt[0]}", lo, hi, cat)
    z = prob.add_variable("z", -3, 4); prob += z
    m = {0: N - 1.0, 1: 1.0}; rho = {1: 1}; hist = []
    slack = N - T - 1.0; lam = 1.0 / (N - T)
    for e in range(1, E):                      # reply index e+1
        b = 1 << e; r = e + 1
        types = sorted(m); ub = {J: (1.0 if J else N) for J in types}
        s = {J: V(0, ub[J]) for J in types}
        for J in types: prob += s[J] <= m[J]
        prob += pulp.lpSum(s.values()) == T
        a = {J: m[J] - s[J] for J in types}
        o = {}
        if r == w:                             # swap round
            prob += a[0] + a[1] == q0
            th = slack / (N - T - q0)          # fraction omitted from every other class
            for J in types: o[J] = 0 if J in (0, 1) else th * a[J]
        elif r in (2, 3) and r < w:            # omit pool first, then lowest degree
            ov = {J: V(0, ub[J]) for J in types}
            for J in types: prob += ov[J] <= a[J]
            prob += pulp.lpSum(ov.values()) == slack
            pre = []
            for J in LOW(types):
                pre.append(J); g = V(cat="Binary")
                prob += a[J] - ov[J] <= ub[J] * g
                prob += slack - pulp.lpSum(ov[K] for K in pre) <= slack * (1 - g)
            o = ov
        else:
            for J in types: o[J] = (1 - lam) * a[J]
        m2, rho2 = {}, dict(rho)
        for J in types:
            m2[J] = s[J] + o[J]; m2[J | b] = a[J] - o[J]
            rr = V(cat="Binary"); prob += a[J] <= ub[J] * rr; rho2[J | b] = rr
        hist.append(s); m, rho = m2, rho2
    full = (1 << E) - 1; I = full & ~(1 << (drop - 1)); delta = {}
    for P in range(full + 1):
        if P & ~I: continue
        comp = I & ~P
        if comp == 0: delta[P] = 1; continue
        dv = V(cat="Binary"); delta[P] = dv
        for K, rk in rho.items():
            if K and (K & comp) == comp:
                if isinstance(rk, int):
                    if rk: prob += dv >= 1
                else: prob += dv >= rk
    tot = []
    for J, mj in m.items():
        dl = delta[J & I]
        if isinstance(dl, int): tot.append(mj)
        else:
            d = V(0, N); prob += d >= mj - (N if J == 0 else 1.0) * (1 - dl); tot.append(d)
    prob += pulp.lpSum(tot) <= T + z
    res = prob.solve(pulp.HiGHS(msg=msg, timeLimit=tl, threads=1))
    if not res.has_solution: return res.status_str, None, res.best_bound, None
    sol = [{str(J): round(pulp.value(v), 9) for J, v in s.items() if pulp.value(v) > 1e-9} for s in hist]
    return res.status_str, pulp.value(z), res.best_bound, sol

def rule_step(m, s, N, r, w, exact):
    """Apply the adversary's true rule at reply r to state m with request s.  Returns (omission dict)."""
    Z = Fr(0) if exact else 0.0; one = Fr(1) if exact else 1.0
    tot = sum(s.values()); a = {J: m[J] - s[J] for J in m}; slack = N - tot - 1
    o = {J: Z for J in m}
    if r == w:
        q = a.get(0, Z) + a.get(1, Z)
        if q <= 1:
            rest = N - tot - q
            th = slack / rest if rest > 0 else Z
            for J in m:
                if J not in (0, 1): o[J] = th * a[J]
        else:                                   # pool first, then B_1-only, nothing else
            take0 = min(a.get(0, Z), one); take1 = one - take0
            for J in m: o[J] = a[J]
            o[0] = a.get(0, Z) - take0
            if 1 in m: o[1] = a[1] - take1
    elif r in (2, 3) and r < w:
        left = slack
        for J in LOW(sorted(m)):
            x = min(left, a[J]); o[J] = x; left -= x
    else:
        lam = 1 / (N - tot)
        for J in m: o[J] = (1 - lam) * a[J]
    return a, o

def simulate(d, exact=False, margin=0.0, eps=2e-6):
    """Replay a line.  exact: Fractions, requests snapped (whole type / zero within 3e-5, else rationalised)."""
    N = Fr(d["N"]).limit_denominator(10**4) if exact else d["N"]; w = d["w"]; E = 7
    m = {0: N - 1, 1: Fr(1) if exact else 1.0}; real = {1}; hist = []
    for e in range(1, E):
        b = 1 << e; sf = d["sol"][e - 1]; s = {}
        for J, mj in m.items():
            x = float(sf.get(str(J), 0.0))
            if exact: s[J] = mj if x >= float(mj) - 3e-5 else (Fr(0) if x < 3e-5 else Fr(x).limit_denominator(10**6))
            else: s[J] = min(mj, x)
        if exact:
            Tt = Fr(d["T"]).limit_denominator(10**4) + Fr(margin).limit_denominator(10**6)
            assert sum(s.values()) <= Tt, f"over budget at reply {e+1}"
        a, o = rule_step(m, s, N, e + 1, w, exact)
        hist.append((dict(m), dict(s)))
        m2 = {}
        for J in m:
            m2[J] = s[J] + o[J]
            if (a[J] > 0) if exact else (a[J] > eps):
                real.add(J | b)
                if (a[J] - o[J] > 0) if exact else (a[J] - o[J] > eps): m2[J | b] = a[J] - o[J]
        m = m2 if exact else {J: v for J, v in m2.items() if v > eps or J == 0}
        if exact: assert sum(v for J, v in m.items() if J & b) == 1
    return m, real, hist

def exact_value(d, margin=0.001):
    m, real, _ = simulate(d, exact=True, margin=margin)
    T = Fr(d["T"]).limit_denominator(10**4) + Fr(margin).limit_denominator(10**6); best = None
    for drop in range(7):
        I = 127 & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        if best is None or D - T < best[0]: best = (D - T, drop + 1)
    return best

if __name__ == "__main__":
    # py swap.py worker_index : scan (N, w, q0, drop) at budget 0.759, verify exactly at T = 0.76
    wk = int(sys.argv[1]); out = open(f"swap_{wk}.log", "a")
    jobs = [(N, w) for w in (4, 5, 6) for N in (1.8, 1.85, 1.9)]
    jobs = [j for i, j in enumerate(jobs) if i % 2 == wk]
    for N, w in jobs:
        won = False; t0 = time.time()
        for drop in (5, 4, 6, 3, 7):
            for q0 in (0.0, 0.05, 0.15, 0.3):
                if won or time.time() - t0 > 600: break
                st, zv, bd, sol = solve(0.759, N, w, q0, drop, tl=70)
                rec = dict(T=0.759, N=N, w=w, q0=q0, drop=[drop], status=st, z=zv, bound=bd, sol=sol)
                if zv is not None and zv < -0.0015:
                    try:
                        ze, de = exact_value(rec); rec["exact_z_float"] = float(ze); rec["exact_z_at_T"] = str(ze); rec["exact_drop"] = de
                        won = ze < 0
                    except AssertionError as ex: rec["exact_error"] = str(ex)
                out.write(json.dumps(rec) + "\n"); out.flush()
        out.write(json.dumps(dict(SUMMARY=True, N=N, w=w, verdict="REQUESTER wins (exact line)" if won else "no line found", secs=round(time.time() - t0))) + "\n"); out.flush()
