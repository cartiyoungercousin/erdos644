"""PETAL §31(b): the trace adversary A_T on point sets, and its legality check.

A_T answers every request S with a member of H(k; nA, nF, d, d, m) avoiding S:
  class choice: class A when feasible (and fewer than 4 class-A replies so far, or class F infeasible), else class F;
  class-A reply: k - d points of R_A minus S (lowest index first), leak = d fresh R_F points (never used, not in S);
      if fresh R_F points run out: fresh pool points, then any R_F point outside S ("all-singles in R_F");
  class-F reply: keeps EVERY unrequested single (class-A leak point in R_F outside S); trace size
      theta = min(d, k - #unrequested singles); trace points of R_A minus S by priority
        (1) points of earlier class-F traces (a point in two centres; the requester must have sealed them),
        (2) points of pair cells, (3) points of triple cells, (4) other points
      (cells read off the first four class-A replies); R_F part = the singles + filler from R_F minus S.
Legality = every reply is a k-set, avoids S, and has >= k - d points in its own arena.  The harness plays A_T against
  (i) the PS3 strategy of ps3.py (forced petals, forced centres), and (ii) random requests of every profile
  (|S cap R_A|, |S cap R_F|, |S cap O|) with |S| <= T, including unforced ones,
and reports any illegal reply and any request that A_T cannot answer although some member avoids S.
Usage: py trace_adversary.py
"""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(__file__))
from pool_strip import Fam, two_cover


class TraceAdversary:
    def __init__(s, F):
        s.F = F; s.reps = []; s.cls = []; s.used = set()

    def singles(s):
        A = [E for E, c in zip(s.reps, s.cls) if c == 0]
        out = set()
        for E in A:
            out |= (E & s.F.R[1])
        return out

    def cells(s):
        A = [E for E, c in zip(s.reps, s.cls) if c == 0][:4]
        if len(A) < 4: return {}
        return {x: sum(1 for E in A if x in E) for x in s.F.R[0]}

    def reply_A(s, S):
        F, k, d = s.F, s.F.k, s.F.d[0]
        RA = sorted(F.R[0] - S)
        if len(RA) < k - d: return None
        E = set(RA[:k - d])
        fresh = [x for x in sorted(F.R[1] - S) if x not in s.used]
        fresh += [x for x in sorted(F.R[2] - S) if x not in s.used]
        fresh += [x for x in sorted(F.R[1] - S) if x in s.used]
        fresh += [x for x in RA[k - d:]]
        if len(fresh) < d: return None
        return E | set(fresh[:d])

    def reply_F(s, S):
        F, k, d = s.F, s.F.k, s.F.d[1]
        sing = s.singles() - S
        RF = F.R[1] - S
        if len(RF) < k - d: return None
        theta = min(d, max(0, k - len(sing)))   # room left for the trace after keeping every unrequested single
        theta = max(theta, k - len(RF))          # not enough R_F room: more leak
        if theta > d: return None
        cell = s.cells()
        earlier = set()
        for E, c in zip(s.reps, s.cls):
            if c == 1: earlier |= (E & F.R[0])
        RA = F.R[0] - S
        pri = lambda x: (0 if x in earlier else 1 + {2: 0, 3: 1}.get(cell.get(x, 0), 2), x)
        leak = sorted(RA, key=pri)[:theta]
        if len(leak) < theta: leak += sorted(F.R[2] - S)[:theta - len(leak)]
        if len(leak) < theta:                     # no room outside R_F: take more R_F instead
            theta = len(leak)
            if k - theta > len(RF): return None
        Fpart = set(sorted(sing)[:k - theta])
        Fpart |= set(sorted(RF - Fpart)[:k - theta - len(Fpart)])
        return set(leak) | Fpart

    def ask(s, S):
        nA = sum(1 for c in s.cls if c == 0)
        order = (0, 1) if nA < 4 else (1, 0)
        for c in order:
            E = s.reply_A(S) if c == 0 else s.reply_F(S)
            if E is not None and len(E) == s.F.k:
                s.reps.append(E); s.cls.append(c); s.used |= E
                return E
        return None


def legal(F, S, E):
    return E is not None and len(E) == F.k and not (E & S) and bool(F.classes(E))


def exists_member(F, S):
    return F.feasible(S, 0) or F.feasible(S, 1)


def random_game(F, T, rnd, rounds=7):
    adv = TraceAdversary(F); bad = []
    for _ in range(rounds):
        a = rnd.randint(0, min(T, F.n[0])); f = rnd.randint(0, min(T - a, F.n[1])); o = rnd.randint(0, min(T - a - f, F.m))
        pool = [sorted(F.R[0]), sorted(F.R[1]), sorted(F.R[2])]
        # bias: sometimes request earlier replies' points
        prev = set().union(*adv.reps) if adv.reps else set()
        S = set()
        for reg, cnt in zip(range(3), (a, f, o)):
            cand = pool[reg]
            hot = [x for x in cand if x in prev]
            rnd.shuffle(hot); cold = [x for x in cand if x not in prev]; rnd.shuffle(cold)
            S |= set((hot + cold)[:cnt] if rnd.random() < .5 else (cold + hot)[:cnt])
        E = adv.ask(S)
        if E is None:
            if exists_member(F, S): bad.append(("unanswered", len(S)))
            break
        if not legal(F, S, E): bad.append(("illegal", len(S)))
    return bad


if __name__ == "__main__":
    from ps3 import ps3_strategy
    INST = [(40, 30, 9, 12), (40, 30, 9, 0), (80, 60, 19, 40), (80, 61, 18, 40), (100, 76, 23, 60), (100, 77, 22, 0)]
    for (k, T, d, m) in INST:
        tA = T // 2 + 1
        nA = tA - 1 + k - d
        F = Fam(k, nA, nA, d, d, m)
        rnd = random.Random(k * 7 + d)
        # (i) against PS3
        adv = TraceAdversary(F)
        reqs = []
        def ask(S, adv=adv):
            reqs.append(S); E = adv.ask(S)
            if E is not None and not legal(F, S, E): raise SystemExit("ILLEGAL reply vs PS3 at k=%d" % k)
            return E
        res = ps3_strategy(F, T, ask, 0)
        reps = res["reps"]
        cov = two_cover(reps) if len(reps) == 7 else "n/a"
        over = sum(1 for S in reqs if len(S) > T)
        # (ii) random requests
        bad = []
        for g in range(400):
            bad += random_game(F, T, rnd)
        print("k=%d T=%d d=%d (delta=%.3f, 1-t=%.3f) m=%d | vs PS3: %d replies legal, over-T requests %d, 2-cover %s, "
              "flags %s | random: 400 games, problems %d %s" % (
                  k, T, d, d / k, 1 - T / k, m, len(reps), over, cov is not None, sorted(set(res["flags"])), len(bad),
                  bad[:3]), flush=True)
