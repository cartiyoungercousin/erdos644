"""PETAL §45.2: fixed-family (7,2) test of pooled A and its natural tau > T subfamilies at the smallest strip instances.

Strip: 3/4 <= t < 7/9, t/2 - 1/6 <= delta < 1 - t (t = T/k, delta = d/k).  Arenas R_A, R_F with tau_A + tau_F = T + 1,
tau_c = n_c - k + d + 1; pool O.
Families (class c member = k-set; 'own' = R_c, c' = other class):
  H     : >= k - d in R_c, the rest anywhere (pooled A, PETAL §29)
  Hnp   : H without pool (m = 0)                       -- the family the §31 adversary A_T answers from
  Hex   : exactly k - d in R_c and exactly d in R_c'   -- A_T's class-A replies; no pool
  Hpo   : exactly k - d in R_c and exactly d in O, |O| = T + d (least pool keeping tau > T); no cross leak
For each: tau by exhaustive profile enumeration (membership-avoidance depends only on the profile of S), and a SAT search
(CaDiCaL) for seven distinct members, pattern 4 class A + 3 class F, with no 2-point cover; the seven are re-checked by
the plain double loop over points (pool_strip.two_cover).
Usage: py fixed72_strip.py
"""
import sys, os, itertools, time
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "petal5"))
from pool_strip import two_cover
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


class Inst:
    def __init__(s, k, T, d, nA, nF, m):
        s.k, s.T, s.d, s.n, s.m = k, T, d, [nA, nF], m
        s.R = [list(range(nA)), list(range(nA, nA + nF)), list(range(nA + nF, nA + nF + m))]
        s.N = nA + nF + m


# a family = for each class c, a list of (region index, lo, hi) count constraints; regions 0 = R_A, 1 = R_F, 2 = O
def fam_rules(name, I):
    k, d = I.k, I.d
    if name in ("H", "Hnp"):
        return {c: [(c, k - d, k)] for c in (0, 1)}
    if name == "Hex":
        return {c: [(c, k - d, k - d), (1 - c, d, d), (2, 0, 0)] for c in (0, 1)}
    if name == "Hpo":
        return {c: [(c, k - d, k - d), (1 - c, 0, 0), (2, d, d)] for c in (0, 1)}
    raise ValueError(name)


def avoid_ok(I, rules, free):
    """some member of the class avoids S iff the free counts allow the constraints (sizes add to k)"""
    for c, rl in rules.items():
        lo = [0, 0, 0]; hi = [free[0], free[1], free[2]]
        for (r, a, b) in rl:
            lo[r] = max(lo[r], a); hi[r] = min(hi[r], b)
        if all(lo[r] <= hi[r] for r in range(3)) and sum(lo) <= I.k <= sum(hi):
            return True
    return False


def tau_profile(I, rules):
    best = None
    for a in range(I.n[0] + 1):
        for f in range(I.n[1] + 1):
            if best is not None and a + f >= best: break
            for o in range(I.m + 1):
                if best is not None and a + f + o >= best: break
                if not avoid_ok(I, rules, [I.n[0] - a, I.n[1] - f, I.m - o]):
                    best = a + f + o
                    break
    return best


def sat7(I, rules, timeout=600):
    N = I.N
    vp = IDPool(); x = lambda j, p: vp.id(("x", j, p))
    cnf = CNF()
    cls = [0, 0, 0, 0, 1, 1, 1]
    for j in range(7):
        for cl in CardEnc.equals([x(j, p) for p in range(N)], I.k, vpool=vp, encoding=EncType.seqcounter).clauses:
            cnf.append(cl)
        for (r, lo, hi) in rules[cls[j]]:
            lits = [x(j, p) for p in I.R[r]]
            if hi == 0:
                for l in lits: cnf.append([-l])
                continue
            if lo > 0:
                for cl in CardEnc.atleast(lits, lo, vpool=vp, encoding=EncType.seqcounter).clauses: cnf.append(cl)
            if hi < len(lits):
                for cl in CardEnc.atmost(lits, hi, vpool=vp, encoding=EncType.seqcounter).clauses: cnf.append(cl)
    for j in range(7):
        for jj in range(j + 1, 7):
            ds = []
            for p in range(N):
                dv = vp.id(("d", j, jj, p))
                cnf.append([-dv, x(j, p)]); cnf.append([-dv, -x(jj, p)]); ds.append(dv)
            cnf.append(ds)
    for p in range(N):
        for q in range(p, N):
            ys = []
            for j in range(7):
                y = vp.id(("y", j, p, q))
                cnf.append([-y, -x(j, p)]); cnf.append([-y, -x(j, q)]); ys.append(y)
            cnf.append(ys)
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=cnf.clauses) as s:
        if not s.solve(): return None, time.time() - t0
        mdl = set(l for l in s.get_model() if l > 0)
    return [set(p for p in range(N) if x(j, p) in mdl) for j in range(7)], time.time() - t0


def member_ok(I, rules, c, E):
    cnt = [len(E & set(I.R[r])) for r in range(3)]
    return len(E) == I.k and all(lo <= cnt[r] <= hi for (r, lo, hi) in rules[c])


def instances():
    """smallest integer instances of the strip (t in [3/4, 7/9), delta in [t/2 - 1/6, 1 - t)), plus the first one with
    delta > 3t/10 (the region where the forced-centre model of §31 is an adversary win)."""
    from fractions import Fraction as Fr
    out = []
    for k in range(8, 60):
        for T in range(1, k):
            t = Fr(T, k)
            if not (Fr(3, 4) <= t < Fr(7, 9)): continue
            for d in range(1, k):
                dl = Fr(d, k)
                if t / 2 - Fr(1, 6) <= dl < 1 - t:
                    out.append((k, T, d))
    return out


if __name__ == "__main__":
    allinst = instances()
    print("strip instances with k < 60 (k, T, d):", allinst)
    chosen = [(24, 18, 5), (33, 25, 7), (37, 28, 8), (44, 33, 10)]
    first310 = [z for z in allinst if 10 * z[2] > 3 * z[1]]
    chosen += [z for z in first310 if 4 * z[1] > 3 * z[0]][:1]   # first with t > 3/4 and delta > 3t/10
    for (k, T, d) in chosen:
        S = 2 * k - 2 * d + T - 1          # nA + nF so that tau_A + tau_F = T + 1
        nA, nF = (S + 1) // 2, S // 2
        t, dl = T / k, d / k
        print("\n(k,T,d)=(%d,%d,%d): t=%.4f delta=%.4f  t/2-1/6=%.4f 3t/10=%.4f 1-t=%.4f  nA=%d nF=%d" %
              (k, T, d, t, dl, t / 2 - 1 / 6, 0.3 * t, 1 - t, nA, nF), flush=True)
        for name, m in (("H", 2 * d), ("Hnp", 0), ("Hex", 0), ("Hpo", T + d)):
            I = Inst(k, T, d, nA, nF, m)
            rules = fam_rules(name, I)
            tau = tau_profile(I, rules)
            sets, dt = sat7(I, rules)
            if sets is None:
                print("  %-4s m=%3d tau=%d: SAT 4A+3F no-2-cover: UNSAT (%.1fs)" % (name, m, tau, dt), flush=True)
                continue
            ok = all(member_ok(I, rules, c, E) for c, E in zip([0] * 4 + [1] * 3, sets))
            distinct = len({frozenset(E) for E in sets}) == 7
            cov = two_cover(sets)
            prof = [[len(E & set(I.R[r])) for r in range(3)] for E in sets]
            print("  %-4s m=%3d tau=%d (T+1=%d): seven found in %.1fs; members legal %s, distinct %s, brute-force 2-cover %s;"
                  " profiles %s" % (name, m, tau, T + 1, dt, ok, distinct, cov, prof), flush=True)
