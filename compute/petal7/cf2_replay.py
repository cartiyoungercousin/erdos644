"""PETAL §46.3: CF2 = centres first, then petals with slack, following the cf_lp.py pattern; exact replay.
Centres as cf_replay.cf_strategy.  Types of R_F points after the centres: Tri (in all three), kappa_j (missed by centre j
only), low.  Petal a = 0, 1, 2 excludes kappa_a: Y_a = Tri + kappa_a (+ padding by earlier leak points), window
W_a = z_a + a private block of non-trace R_A points (largest the budget allows).  Petal 3 excludes nothing: W_3 = the
uncovered non-trace points (+ padding by non-trace points already in a window), Y_3 = Tri + earlier leak points (points in
two earlier leaks first) + padding.  Every request <= T; certificate by the plain 2-cover double loop.
Usage: py cf2_replay.py
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__)); sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "petal5"))
from pool_strip import Fam, two_cover
from trace_adversary import TraceAdversary, legal
from cf_replay import LeakAware, INST


def cf2(F, T, ask):
    k = F.k; tA, tF = F.tau_c(0), F.tau_c(1)
    RA, RF, O = sorted(F.R[0]), sorted(F.R[1]), F.R[2]
    reqs, reps, flags, cent = [], [], [], []
    blk = tF - 1
    Ks = [RF[:blk], RF[blk:2 * blk], RF[2 * blk:] + RF[:blk]]
    for j in range(3):
        G = set().union(*[C & F.R[0] for C in cent]) if cent else set()
        for x in RA:
            if len(G) >= tA: break
            G.add(x)
        S = G | ((cent[0] & cent[1] & O) if j == 2 else set())
        S |= set([x for x in Ks[j] if x not in S][:max(0, T - len(S))])
        reqs.append(S); E = ask(S)
        if E is None or F.classes(E) != [1]: flags.append("centre"); return dict(reqs=reqs, reps=reps + [E] if E else reps, flags=flags)
        cent.append(E); reps.append(E)
    z = [sorted(C & F.R[0]) for C in cent]
    c = {y: frozenset(j for j in range(3) if y in cent[j]) for y in RF}
    tri = [y for y in RF if len(c[y]) == 3]
    kap = [[y for y in RF if c[y] == frozenset({0, 1, 2}) - {j}] for j in range(3)]
    U0 = [x for x in RA if not any(x in zz for zz in z)]
    p = [max(0, T - len(z[a]) - max(tF, len(tri) + len(kap[a]))) for a in range(3)]
    W, pos = [], 0
    for a in range(3):
        W.append(set(z[a]) | set(U0[pos:pos + p[a]])); pos += p[a]
    unc = U0[pos:]
    pet = []
    for a in range(4):
        leaks = [P - F.R[0] for P in pet]
        mult = {y: sum(y in L for L in leaks) for y in RF}
        if a < 3:
            Y = list(tri) + kap[a]
            Wa = W[a]
        else:
            Wa = set(unc)
            for x in U0:                       # pad with non-trace points already in a window (pair cells)
                if len(Wa) >= T - tF: break
                Wa.add(x)
            Y = list(tri)
        for y in sorted(RF, key=lambda y: (-mult[y], y)):
            if len(Y) >= T - len(Wa): break
            if y not in Y and (mult[y] > 0 or a < 3): Y.append(y)
        for y in RF:
            if len(Y) >= max(tF, T - len(Wa)): break
            if y not in Y: Y.append(y)
        S = set(Wa) | set(Y)
        if len(S) > T: flags.append("over T")
        reqs.append(S); E = ask(S)
        if E is None or F.classes(E) != [0]: flags.append("petal %s" % (None if E is None else F.classes(E))); return dict(reqs=reqs, reps=reps, flags=flags)
        pet.append(E); reps.append(E)
    if set().union(*[F.R[0] - P for P in pet]) != F.R[0]: flags.append("windows do not cover")
    if set.intersection(*pet): flags.append("petals meet")
    return dict(reqs=reqs, reps=reps, flags=flags)


if __name__ == "__main__":
    for (k, T, d, m) in INST:
        S = 2 * k - 2 * d + T - 1
        F = Fam(k, (S + 1) // 2, S // 2, d, d, m)
        for name, mk in (("A_T", lambda: TraceAdversary(F)), ("A_T+", lambda: LeakAware(F)), ("A_T+p", lambda: LeakAware(F, True))):
            adv = mk()
            def ask(S, adv=adv):
                E = adv.ask(S)
                if E is not None and not legal(F, S, E): raise SystemExit("illegal reply")
                return E
            r = cf2(F, T, ask)
            reps = r["reps"]
            cov = two_cover(reps) if len(reps) == 7 else "n/a"
            print("k=%d T=%d d=%d m=%d vs %-5s: sizes %s | 2-cover %s | flags %s" % (k, T, d, m, name, [len(R) for R in r["reqs"]], cov, r["flags"]), flush=True)
