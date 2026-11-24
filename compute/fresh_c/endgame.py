r"""
Six-edge endgame of the request game (scale-free, masses in units of k).

Points are typed by J = set of edges among A_1..A_6 containing them (bitmask).  State after i edges:
mass m[J] >= 0 and a 'realized' flag rho[J] (a type can be realized by O(1) points = mass 0).
Round i+1: requester picks s[J] <= m[J], sum s <= T.  Adversary picks y[J] <= m[J]-s[J], fresh f >= 0,
sum y + f = 1; type J|{i+1} gets mass y[J] and is REALIZED iff m[J]-s[J] > 0 (one unrequested point suffices;
zero-mass realized types are requested for free and never promoted).  Fresh type {i+1} is always realized.
Terminal: D = union of types J whose complement [6]\J is contained in some realized type
(exactly the points that A_7 may not contain: y in A_7 with pattern J plus a partner x with pattern
J' >= [6]\J is a 2-cover).  Requester wins iff mass(D) <= T and type [6] is not realized.

Exact MILPs:
  mode 'adv_free': requester follows a priority policy (given order of types each round, greedy fill);
                   adversary optimises -> max mass(D).
  mode 'req_free': adversary follows a priority policy (greedy fill of the new edge in a given order,
                   optional per-type caps); requester optimises -> min mass(D).
"""
import pulp, sys, time

def popc(x): return bin(x).count("1")
def tstr(J): return "".join(str(i + 1) for i in range(6) if (J >> i) & 1) or "0"

def solve(T, mode, req_order=None, adv_order=None, req_ties="order", tl=300, msg=False, adv_take=None,
          RBIG=1e4, N=None, pool_first=False):
    """req_order(i, types) / adv_order(i, types): sorted list of the types on [i] (bitmasks) for round i+1.
    req_ties: 'order' (strict priority list) or 'degree' (only degree classes fixed, ties left to optimiser).
    adv_take(i, J) -> bool: whether the policy adversary promotes mass from type J in round i+1."""
    prob = pulp.LpProblem("endgame", pulp.LpMaximize if mode == "adv_free" else pulp.LpMinimize)
    V = lambda nm, lo=0, hi=None, cat="Continuous": prob.add_variable(nm, lo, hi, cat)
    m = {1: {1: 1.0}}
    rho = {1: {1: 1}}
    M = 3.0
    for i in range(1, 6):
        b = 1 << i
        types = sorted(m[i].keys())
        s = {J: V(f"s{i}_{J}", 0, 1) for J in types}
        y = {J: V(f"y{i}_{J}", 0, 1) for J in types}
        f = V(f"f{i}", 0, 1)
        if N is not None:                      # bounded ground set of mass N: pool of untouched points
            pool = N - pulp.lpSum(m[i][J] for J in types)
            s0 = V(f"s0_{i}", 0, N)
            prob += s0 <= pool
            a0 = pool - s0
            prob += f <= a0
        else:
            s0 = 0
        a = {J: m[i][J] - s[J] for J in types}
        for J in types:
            prob += s[J] <= m[i][J]
            prob += y[J] <= a[J]
        prob += pulp.lpSum(s.values()) + s0 <= T
        prob += pulp.lpSum(y.values()) + f == 1
        # requester policy
        if mode == "adv_free":
            order = req_order(i, types)
            for idx, J in enumerate(order):
                h = V(f"h{i}_{J}", cat="Binary")       # h=1: J not fully requested => budget exhausted on earlier
                prob += a[J] <= M * h
                if req_ties == "order":
                    pre = order[: idx + 1]
                else:
                    pre = [K for K in order if popc(K) >= popc(J)]
                prob += T - pulp.lpSum(s[K] for K in pre) <= M * (1 - h)
        # adversary policy
        if mode == "req_free":
            order = adv_order(i, types)
            used = []
            if N is not None and pool_first:   # adversary fills from the untouched pool first
                g0 = V(f"g0_{i}", cat="Binary")
                prob += a0 - f <= (N + 1) * g0
                prob += 1 - f <= M * (1 - g0)
            ysum_extra = f if (N is not None and pool_first) else 0
            for J in order:
                if adv_take is not None and not adv_take(i, J):
                    prob += y[J] == 0
                    continue
                used.append(J)
                g = V(f"g{i}_{J}", cat="Binary")       # g=1: J not fully taken => edge already full
                prob += a[J] - y[J] <= M * g
                prob += 1 - pulp.lpSum(y[K] for K in used) - ysum_extra <= M * (1 - g)
            if N is not None and not pool_first:                  # pool is last in the greedy order
                g0 = V(f"g0_{i}", cat="Binary")
                prob += a0 - f <= (N + 1) * g0
                prob += 1 - pulp.lpSum(y[K] for K in used) - f <= M * (1 - g0)
        m[i + 1] = {}
        rho[i + 1] = {}
        for J in types:
            m[i + 1][J] = m[i][J] - y[J]
            m[i + 1][J | b] = y[J]
            rho[i + 1][J] = rho[i][J]
            r = V(f"r{i+1}_{J|b}", cat="Binary")
            if mode == "adv_free":
                prob += r <= RBIG * a[J]
            else:
                prob += r >= a[J]
            rho[i + 1][J | b] = r
        m[i + 1][b] = f
        rho[i + 1][b] = 1
    # terminal
    dvars = []
    for J in range(1, 64):
        comp = 63 ^ J
        sup = [K for K in range(1, 64) if (K & comp) == comp]
        dl = V(f"dl_{J}", cat="Binary")
        d = V(f"d_{J}", 0, 1)
        if mode == "adv_free":
            prob += dl <= pulp.lpSum(rho[6][K] for K in sup)
            prob += d <= m[6][J]
            prob += d <= dl
        else:
            for K in sup:
                prob += dl >= rho[6][K]
            prob += d >= m[6][J] - (1 - dl)
        dvars.append(d)
    prob += pulp.lpSum(dvars) + 10 * rho[6][63]
    res = prob.solve(pulp.HiGHS(msg=msg, timeLimit=tl))
    st = res.status_str
    if not res.has_solution:
        return st, None, None
    val = pulp.value(prob.objective)
    val_f = lambda e: e if isinstance(e, (int, float)) else pulp.value(e)
    final = {tstr(J): round(val_f(m[6][J]), 4) for J in range(1, 64) if val_f(m[6][J]) > 1e-6}
    real = sorted(tstr(J) for J in range(1, 64) if val_f(rho[6][J]) > 0.5)
    Dset = sorted(tstr(J) for J in range(1, 64) if pulp.value(prob.variablesDict()[f"dl_{J}"]) > 0.5)
    hist = []
    for i in range(1, 6):
        vd = prob.variablesDict()
        hist.append(dict(
            req={tstr(J): round(pulp.value(vd[f"s{i}_{J}"]), 4) for J in sorted(m[i]) if pulp.value(vd[f"s{i}_{J}"]) > 1e-6},
            take={tstr(J): round(pulp.value(vd[f"y{i}_{J}"]), 4) for J in sorted(m[i]) if pulp.value(vd[f"y{i}_{J}"]) > 1e-6},
            fresh=round(pulp.value(vd[f"f{i}"]), 4)))
    return st, val, dict(final=final, realized=real, D=Dset, hist=hist, bound=res.best_bound)

def by_degree(i, types):          # top-degree, ties lexicographic
    return sorted(types, key=lambda J: (-popc(J), J))

if __name__ == "__main__":
    T = float(sys.argv[1]); mode = sys.argv[2]; ties = sys.argv[3] if len(sys.argv) > 3 else "order"
    t0 = time.time()
    if mode == "adv_free":
        st, val, info = solve(T, "adv_free", req_order=by_degree, req_ties=ties)
    else:
        Nv = float(sys.argv[4]) if len(sys.argv) > 4 else None
        st, val, info = solve(T, "req_free", adv_order=by_degree, N=Nv)
    print(f"T={T} mode={mode} ties={ties}: status={st} mass(D)={val}  [{time.time()-t0:.1f}s]")
    if info:
        print(" final types:", info["final"]); print(" realized:", info["realized"]); print(" D types:", info["D"])
        for i, h in enumerate(info["hist"], start=2):
            print(f"  edge {i}: request {h['req']}  take {h['take']} fresh {h['fresh']}")
