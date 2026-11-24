"""CORE Part VI: certified lower bound for the two-stage game value (her best guaranteed `need` after reply 4).

Adversary restricted to a piecewise-LINEAR menu (a restriction on HIM, so a lower bound proved here holds for his full
legal reply class).  At reply 3 over the 4 types, at reply 4 over the 8 types:
  prop      : the proportional dump;
  (J, a)    : all of omega on type J                               (available iff free_J >= omega);
  (J, J2, b): all of the free part of J, the rest of omega on J2   (iff free_J <= omega <= free_J + free_J2),
              J2 = the other type of highest / of lowest co-degree.
Her side is exact: one MILP over S3 and (for each reply-3 option) S4, in which every need_R is replaced by finitely
many LP-dual lower bounds
     need_R(mu) >= sum_h mu_h a_h(beta) + t sum(beta) + omega sum_f min(0, 1 + beta_f)      for every beta <= 0,
a_h(beta) = min over admissible extensions E of -sum_{f in E} beta_f.  [weak duality]  A reading may be used only if its
dead types (no admissible extension) carry mass 0 (exact indicator constraint).
Here need_R is the PENALISED need (line mass beyond t + omega allowed at cost PEN per unit): it is <= the capped need of
twostage.py and equal to it whenever the capped LP is feasible and PEN exceeds its duals; so the bound stays valid.
Hence  (MILP lower bound)  <=  inf of her value against the menu  <=  true two-stage value.
Cutting loop: solve, evaluate the true LPs at her MILP point, add the violated duals, repeat.
Usage: py twostage_cert.py t N o [maxit] [milp_seconds] [s3fix]     s3fix: "sO,sA,sB,sg" to fix her reply-3 request
"""
import sys, json, time, random
import pulp
import twostage as T

DEAD = 3.0; BIGM = 7.0; MA = 2.5; MSG = False; PEN = 5.0; SEEDS = 3000; DEBUG = False


def beta_bound(rd, beta, t, om):
    beta = [max(-PEN, min(0.0, b)) for b in beta]
    alpha = []
    for hh in rd.hs:
        best = None
        for (h2, E) in rd.cols:
            if h2 != hh: continue
            v = -sum(beta[e] for e in E)
            if best is None or v < best: best = v
        alpha.append(0.0 if best is None else best)      # dead types are handled exactly in the MILP (mass must be 0)
    const = t * sum(beta) + om * sum(min(0.0, 1.0 + b) for b in beta)
    return alpha, const


def lp_dual(rd, mu, t, om):
    v, dual = rd.need(mu, want_dual=True)
    beta = [0.0] * len(rd.F) if dual is None else dual[(1 << rd.r):]
    a, c = beta_bound(rd, beta, t, om)
    return v, tuple(round(x, 9) for x in a), round(c, 9)


def popc(x): return bin(x).count("1")


def partners(J, types):
    rest = [K for K in types if K != J]
    hi = max(rest, key=lambda K: (popc(K), K)); lo = min(rest, key=lambda K: (popc(K), K))
    return [hi] if hi == lo else [hi, lo]


def menu(types):
    out = [("prop",)]
    for J in types:
        out.append((J, "a"))
        for J2 in partners(J, types): out.append((J, J2, "b"))
    return out


def dump_of(opt, free, om):
    """numeric or symbolic dump for a menu option"""
    if opt[0] == "prop": return {J: (om / (1 + om)) * free[J] for J in free}
    if opt[-1] == "a": return {J: (om if J == opt[0] else 0.0) for J in free}
    J, J2 = opt[0], opt[1]
    return {K: (free[J] if K == J else (om - free[J] if K == J2 else 0.0)) for K in free}


def main(t, N, o, maxit=60, tl=300, s3fix=None):
    G = T.Game(t, N, pen=PEN); c = N - 1; om = G.om
    m2 = {3: o, 1: c - o, 2: c - o, 0: N - 2 * c + o}
    rds = G.readings
    cuts = {i: set() for i in range(len(rds))}
    rng = random.Random(0)
    for _ in range(SEEDS):
        s3 = dict(s3fix) if (s3fix and rng.random() < 0.8) else G.norm(m2, {J: rng.random() * m2[J] for J in m2}); d3 = rng.choice(G.dump_menu(m2, s3))
        m3 = G.step(m2, s3, d3, 4)
        s4 = rng.choice(G.line_cands(m3)) if rng.random() < 0.4 else G.norm(m3, {J: (rng.random() ** 2) * m3[J] * (rng.random() < 0.6) for J in m3}); d4 = rng.choice(G.dump_menu(m3, s4))
        m4 = G.step(m3, s4, d4, 8)
        for i, rd in enumerate(rds):
            v, a, cc = lp_dual(rd, G.proj(m4, rd.R), t, om); cuts[i].add((a, cc))
    T3 = [0, 1, 2, 3]; T4 = list(range(8)); B3 = menu(T3); B4 = menu(T4)
    tag = f"t{t}_N{N}_o{o}" + ("_fix" if s3fix else "")
    log = open(f"logs/cert2s_{tag}.log", "w")
    def W(d): log.write(json.dumps(d) + "\n"); log.flush(); print(json.dumps(d)[:700], flush=True)
    W(dict(start=True, t=t, N=N, o=o, omega=om, base=G.base, s3fix=s3fix, menu3=len(B3), menu4=len(B4)))
    best_lb = -1.0; t0 = time.time(); true_v = None

    for it in range(maxit):
        prob = pulp.LpProblem("cert", pulp.LpMinimize); cnt = [0]
        def V(lo=0.0, hi=None, cat="Continuous"):
            cnt[0] += 1; return prob.add_variable(f"x{cnt[0]}", lo, hi, cat)
        def C(con): prob.__iadd__(con)
        def avail(opt, free, AV):
            """binary that is 1 iff the option is available (closed conditions); None for prop"""
            if opt[0] == "prop": return None
            a = V(cat="Binary")
            if opt[-1] == "a":
                J = opt[0]; AV[J] = a
                C(free[J] >= om - MA * (1 - a)); C(free[J] <= om + MA * a)
            else:
                J, J2 = opt[0], opt[1]; f = V(cat="Binary")
                C(free[J] <= om + MA * (1 - a)); C(free[J] + free[J2] >= om - MA * (1 - a))
                C(free[J] >= om - MA * (a + f)); C(free[J] + free[J2] <= om + MA * (a + 1 - f))
                C(AV[J] >= 1 - a - f)          # dropped because free_J >= omega  =>  the all-on-J option is in force
            return a
        def AND(a, b):
            if a is None: return b
            if b is None: return a
            x = V(cat="Binary"); C(x >= a + b - 1); C(x <= a); C(x <= b); return x
        def add_reading(i, m, z, act):
            rd = rds[i]; mu = [0] * (1 << rd.r)
            for J, e in m.items():
                hh = 0
                for k, x in enumerate(rd.R):
                    if J >> x & 1: hh |= 1 << k
                mu[hh] = mu[hh] + e
            live = {h2 for (h2, E) in rd.cols}
            for hh in rd.hs:
                if hh not in live and not isinstance(mu[hh], (int, float)):
                    C(mu[hh] <= MA * (1 - z) + (0 if act is None else MA * (1 - act)))
                elif hh not in live and mu[hh] > 1e-9: C(z <= 0)
            for (a, cc) in cuts[i]:
                C(pulp.lpSum(a[hh] * mu[hh] for hh in rd.hs if a[hh] != 0.0) + cc <= v + BIGM * (1 - z) + (0 if act is None else BIGM * (1 - act)))

        v = V(0.0, 3.0); prob += v
        if s3fix: s3 = {J: s3fix[J] for J in m2}
        else:
            s3 = {J: V(0.0, m2[J]) for J in m2}; C(pulp.lpSum(s3.values()) == t)
        free2 = {J: m2[J] - s3[J] for J in m2}
        rec = []; AV3 = {}                                # (opt3, a3, s4 vars, [(opt4, a4)])
        for b in B3:
            a3 = avail(b, free2, AV3); d3 = dump_of(b, free2, om)
            m3 = {}
            for J in m2:
                m3[J | 4] = s3[J] + d3[J]; m3[J] = m2[J] - s3[J] - d3[J]
            s4 = {J: V(0.0, 1.3) for J in m3}
            for J in m3: C(s4[J] <= m3[J] + (0 if a3 is None else MA * (1 - a3)))
            C(pulp.lpSum(s4.values()) == t)
            free3 = {J: m3[J] - s4[J] for J in m3}
            zprev = []
            for i, rd in enumerate(rds):
                if 3 in rd.R: continue
                z = V(cat="Binary"); zprev.append(z); add_reading(i, m3, z, a3)
            r4 = []; AV4 = {}
            for e in B4:
                a4 = avail(e, free3, AV4); d4 = dump_of(e, free3, om); act = AND(a3, a4)
                m4 = {}
                for J in m3:
                    m4[J | 8] = s4[J] + d4[J]; m4[J] = m3[J] - s4[J] - d4[J]
                zs = list(zprev); zidx = {}
                for i, rd in enumerate(rds):
                    if 3 not in rd.R: continue
                    z = V(cat="Binary"); zs.append(z); zidx[i] = z; add_reading(i, m4, z, act)
                C(pulp.lpSum(zs) >= 1)
                r4.append((e, a4, m4, (act, zidx, list(zprev))))
            rec.append((b, a3, s4, r4))
        res = prob.solve(pulp.HiGHS(msg=MSG, timeLimit=tl))
        vmilp = pulp.value(v); status = res.status_str
        vlo = None
        try: vlo = prob.solverModel.getInfo().mip_dual_bound
        except Exception: pass
        if vlo is None and status == "Optimal": vlo = vmilp
        if vlo is not None: best_lb = vlo
        val = lambda x: x if isinstance(x, (int, float)) else (pulp.value(x) or 0.0)
        S3 = {J: max(0.0, val(x)) for J, x in s3.items()}
        f2 = {J: m2[J] - S3[J] for J in m2}
        true_v = -1.0; added = 0; worst_row = None
        for (b, a3, s4, r4) in rec:
            if a3 is not None and val(a3) < 0.5: continue
            d3 = {J: max(0.0, x) for J, x in dump_of(b, f2, om).items()}
            m3 = G.step(m2, S3, d3, 4)
            for J in range(8): m3.setdefault(J, 0.0)
            S4 = {J: min(max(0.0, val(x)), m3[J]) for J, x in s4.items()}
            f3 = {J: m3[J] - S4[J] for J in m3}
            vprev = T.INF
            for i, rd in enumerate(rds):
                if 3 in rd.R: continue
                x, a, cc = lp_dual(rd, G.proj(m3, rd.R), t, om); vprev = min(vprev, x)
                if (a, cc) not in cuts[i]: cuts[i].add((a, cc)); added += 1
            worst = -1.0; wopt = None
            for (e, a4, m4sym, actv) in r4:
                if a4 is not None and val(a4) < 0.5: continue
                d4 = {J: max(0.0, x) for J, x in dump_of(e, f3, om).items()}
                m4 = G.step(m3, S4, d4, 8); ve = vprev
                dev = max(abs(val(m4sym[J]) - m4.get(J, 0.0)) for J in m4sym)
                if dev > 1e-5: W(dict(MISMATCH=True, d3=str(b), d4=str(e), dev=dev, a3=None if a3 is None else val(a3), a4=None if a4 is None else val(a4), act=None if actv is None else val(actv), sym={T.nm(J): round(val(x), 4) for J, x in m4sym.items()}, num=T.fmt(m4)))
                for i, rd in enumerate(rds):
                    if 3 not in rd.R: continue
                    x, a, cc = lp_dual(rd, G.proj(m4, rd.R), t, om); ve = min(ve, x)
                    if (a, cc) not in cuts[i]: cuts[i].add((a, cc)); added += 1
                if DEBUG and ve > (vmilp or 0) + 1e-4:
                    act_, zidx_, zprev_ = actv
                    rows = []
                    for i, rd in enumerate(rds):
                        if 3 not in rd.R: continue
                        mu = G.proj(m4, rd.R)
                        rows.append((i, rd.R, round(val(zidx_[i]), 3), round(max(sum(a[hh] * mu[hh] for hh in rd.hs) + cc for (a, cc) in cuts[i]), 4), round(rd.need(mu), 4)))
                    W(dict(DEBUG=True, d3=str(b), d4=str(e), ve=ve, act=None if act_ is None else val(act_), zprev=[round(val(z), 3) for z in zprev_], rows=rows))
                if ve > worst: worst, wopt = ve, e
            if worst > true_v: true_v = worst; worst_row = dict(d3=str(b), d4=str(wopt), s4=T.fmt(S4), state3=T.fmt(m3))
        W(dict(it=it, status=status, milp_value=vmilp, milp_lower_bound=vlo, true_value_at_point=true_v, new_cuts=added,
               ncuts=sum(len(x) for x in cuts.values()), s3=T.fmt(S3), worst=worst_row, secs=round(time.time() - t0)))
        if vlo is not None and vlo >= G.base - 1e-6: break
        if added == 0 or (status == "Optimal" and true_v <= vmilp + 1e-6): break
    W(dict(SUMMARY=True, t=t, N=N, o=o, omega=om, base=G.base, certified_lower_bound=best_lb,
           gap_in_omega=(G.base - best_lb) / om, last_true_value=true_v, s3fix=s3fix, secs=round(time.time() - t0)))


if __name__ == "__main__":
    a = sys.argv
    fix = None
    if len(a) > 6:
        x = [float(y) for y in a[6].split(",")]; fix = {3: x[0], 1: x[1], 2: x[2], 0: x[3]}
    main(float(a[1]), float(a[2]), float(a[3]), int(a[4]) if len(a) > 4 else 60, float(a[5]) if len(a) > 5 else 300, fix)
