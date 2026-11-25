"""PETAL §45.4: centres-first (CF) play against the §31 adversary A_T and two leak-aware variants; exact replay.

CF (class-F centres first, then four exact class-A petals designed against the observed traces):
  centre j (j = 0, 1, 2): G_j = R_A-traces of earlier centres + filler, |G_j| = max(tau_A, |traces|) (forces class F);
      request 2 also holds the pool points common to centres 0 and 1; the rest of the budget is a block K_j of R_F
      (K_0, K_1, K_2 disjoint), so the centres' R_F parts are spread;
  petal a (a = 0..3), type y = (0, 1, 2, 2): W_a = tau_A - 1 points of R_A (exact own part R_A minus W_a);
      W_0 contains the R_A-trace z_0, W_1 contains z_1, W_2 and W_3 cover z_2 and the rest of R_A;
      Y_a = tau_F points of R_F: first the points missed by centre y(a), then points lying in all three centres.
  Certificate checked by the plain double loop over points (pool_strip.two_cover); every request <= T is checked.
Adversaries: A_T (trace_adversary.TraceAdversary: petal leaks on fresh points), A_T+ (petal leaks on the points lying in
  most centres, ties to points of earlier petal leaks), A_T+p (A_T+ and centre traces in a common pool set first).
Usage: py cf_replay.py
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "petal5"))
from pool_strip import Fam, two_cover
from trace_adversary import TraceAdversary, legal


class LeakAware(TraceAdversary):
    def __init__(s, F, pooltrace=False):
        super().__init__(F); s.pooltrace = pooltrace

    def reply_A(s, S):
        F, k, d = s.F, s.F.k, s.F.d[0]
        RA = sorted(F.R[0] - S)
        if len(RA) < k - d: return None
        E = set(RA[:k - d])
        cent = [R for R, c in zip(s.reps, s.cls) if c == 1]
        pet = [R for R, c in zip(s.reps, s.cls) if c == 0]
        cand = sorted((F.R[1] | F.R[2]) - S, key=lambda x: (-sum(x in C for C in cent), -sum(x in P for P in pet), x))
        if len(cand) < d: return None
        return E | set(cand[:d])

    def reply_F(s, S):
        if not s.pooltrace: return super().reply_F(S)
        F, k, d = s.F, s.F.k, s.F.d[1]
        RF = sorted(F.R[1] - S)
        if len(RF) < k - d: return None
        cent = [R for R, c in zip(s.reps, s.cls) if c == 1]
        cand = sorted((F.R[0] | F.R[2]) - S, key=lambda x: (-sum(x in C for C in cent), 0 if x in F.R[2] else 1, x))
        tr = cand[:d]
        if len(tr) < d: tr += [x for x in RF[k - d:]][:d - len(tr)]
        return set(tr) | set(RF[:k - len(tr)])


SEAL_LEAKS = os.environ.get("SEAL_LEAKS") == "1"   # also seal every earlier leak point (first in Y)


def cf_strategy(F, T, ask):
    k = F.k
    tA, tF = F.tau_c(0), F.tau_c(1)
    RA, RF, O = sorted(F.R[0]), sorted(F.R[1]), F.R[2]
    reqs, reps, flags = [], [], []
    cent = []
    blk = tF - 1
    Ks = [set(RF[:blk]), set(RF[blk:2 * blk]), RF[2 * blk:]]
    for j in range(3):
        G = set().union(*[C & F.R[0] for C in cent]) if cent else set()
        for x in RA:
            if len(G) >= tA: break
            G.add(x)
        seal = (cent[0] & cent[1] & O) if j == 2 else set()
        S = G | seal
        room = T - len(S)
        K = list(Ks[j]) if j < 2 else Ks[2] + RF[:blk]
        S |= set([x for x in K if x not in S][:max(0, room)])   # K_2 = rest of R_F first (keeps Tri small)
        reqs.append(S); E = ask(S)
        if E is None: flags.append("no reply"); return dict(reqs=reqs, reps=reps, flags=flags)
        if F.classes(E) != [1]: flags.append("centre class %s" % F.classes(E))
        cent.append(E); reps.append(E)
    z = [C & F.R[0] for C in cent]
    if (z[0] & z[1]) or (z[0] & z[2]) or (z[1] & z[2]): flags.append("traces meet")
    w = tA - 1
    R0 = [x for x in RA if not any(x in zz for zz in z)]
    W = []
    W0 = set(z[0]) | set(R0[:max(0, w - len(z[0]))]); R0 = [x for x in R0 if x not in W0]
    W1 = set(z[1]) | set(R0[:max(0, w - len(z[1]))]); R0 = [x for x in R0 if x not in W1]
    rest = sorted(z[2]) + R0
    W2 = set(rest[:w]); W3 = set(rest[w:])
    W3 |= set(sorted(W2)[::-1][:max(0, w - len(W3))])
    W = [W0, W1, W2, W3]
    if any(len(x) > w for x in W): flags.append("window over")
    if set().union(*W) != F.R[0]: flags.append("windows do not cover R_A")
    ytype = (0, 1, 2, 2)
    pet = []
    for a in range(4):
        C = cent[ytype[a]]
        miss = [x for x in RF if x not in C]
        tri = [x for x in RF if all(x in CC for CC in cent) and x not in miss]
        mult = {x: sum(x in P for P in pet) for x in RF}
        multi = [x for x in RF if mult[x] >= 2]           # sealing these prevents a leak point in three petals
        Y = []
        for grp in (multi, [x for x in RF if mult[x] == 1] if SEAL_LEAKS else [], miss, tri, RF):
            for x in sorted(grp, key=lambda x: -mult[x]):
                if len(Y) < tF and x not in Y: Y.append(x)
        S = set(W[a]) | set(Y)
        if pet:
            common = set.intersection(*pet) - F.R[0] - F.R[1]
            if common: flags.append("pool common point")
        reqs.append(S); E = ask(S)
        if E is None: flags.append("no reply"); return dict(reqs=reqs, reps=reps, flags=flags)
        if F.classes(E) != [0]: flags.append("petal class %s" % F.classes(E))
        pet.append(E); reps.append(E)
    if set.intersection(*pet): flags.append("petals meet")
    return dict(reqs=reqs, reps=reps, flags=flags)


INST = [(24, 18, 5, 10), (33, 25, 7, 14), (37, 28, 8, 16), (57, 43, 13, 26), (100, 76, 23, 60), (100, 75, 24, 60),
        (100, 75, 24, 0), (200, 150, 49, 100)]

if __name__ == "__main__":
    for (k, T, d, m) in INST:
        S = 2 * k - 2 * d + T - 1
        nA, nF = (S + 1) // 2, S // 2
        F = Fam(k, nA, nF, d, d, m)
        assert F.tau_c(0) + F.tau_c(1) == T + 1
        for name, mk in (("A_T", lambda: TraceAdversary(F)), ("A_T+", lambda: LeakAware(F)),
                         ("A_T+p", lambda: LeakAware(F, True))):
            adv = mk()
            def ask(S, adv=adv):
                E = adv.ask(S)
                if E is not None and not legal(F, S, E): raise SystemExit("illegal reply")
                return E
            res = cf_strategy(F, T, ask)
            reps = res["reps"]
            mx = max(len(R) for R in res["reqs"])
            cov = two_cover(reps) if len(reps) == 7 else "n/a"
            print("k=%d T=%d d=%d m=%d (t=%.3f delta=%.3f) vs %-5s: requests max %d (T=%d) sizes %s | 2-cover %s | flags %s"
                  % (k, T, d, m, T / k, d / k, name, mx, T, [len(R) for R in res["reqs"]], cov, res["flags"]), flush=True)
