"""Theorem AP (23.2) verbatim on point sets, asymmetric arenas allowed.  usage: py ap.py"""
import sys, math, random
from fractions import Fraction as Fr
from common import *


def ap_strategy(fam, T, ask, force_orient=None):
    k = fam.k
    tau = [fam.tau(0), fam.tau(1)]
    R = fam.R
    half = T / 2.0
    reqs, reps, flags = [], [], []
    cls = []

    def classify(E):
        c = fam.cls_of(E)
        if len(c) != 1:
            flags.append("reply class ambiguous %s" % c)
        return c[0] if c else None

    if tau[0] >= half and tau[1] >= half:
        # unforced running intersections, 14.1
        I = {0: None, 1: None}
        mem = {0: [], 1: []}
        X = None
        for step in range(7):
            S = set()
            for c in (0, 1):
                if I[c] is not None:
                    Il = sorted(I[c])
                    S |= set(Il[:min(int(math.floor(half)), len(Il))])
            reqs.append(S)
            E = ask(S)
            if E is None:
                return dict(replies=reps, requests=reqs, flags=flags, trivial=True)
            c = classify(E)
            mem[c].append(E)
            I[c] = set(E) if I[c] is None else I[c] & E
            reps_all = mem
            if len(mem[c]) >= 4 and not (mem[c][0] & mem[c][1] & mem[c][2] & mem[c][3]):
                X = c
                break
        if X is None:
            for c in (0, 1):
                if len(mem[c]) >= 4:
                    X = c
            flags.append("no petal class with empty intersection after 7")
            if X is None:
                return dict(replies=[], requests=reqs, flags=flags)
        petals = mem[X][:4]
    else:
        X = 0 if tau[0] >= half else 1
        Y = 1 - X
        trans = set(sorted(R[Y])[:tau[Y] + 1])
        I = None
        mem = []
        for step in range(7):
            S = set(trans)
            if I is not None:
                Il = sorted(I)
                S |= set(Il[:min(-(-k // 3), len(Il))])
            reqs.append(S)
            E = ask(S)
            if E is None:
                return dict(replies=reps, requests=reqs, flags=flags, trivial=True)
            c = classify(E)
            if c != X:
                flags.append("forced step: reply of class Y")
            mem.append(E)
            I = set(E) if I is None else I & E
            if len(mem) >= 4 and not (mem[0] & mem[1] & mem[2] & mem[3]):
                break
        petals = mem[:4]
        if len(petals) < 4 or (petals[0] & petals[1] & petals[2] & petals[3]):
            flags.append("forced: no empty intersection")
            return dict(replies=[], requests=reqs, flags=flags)
    Y = 1 - X
    U = set().union(*petals)
    B = set()
    for E in petals:
        B |= (E - R[X])
    Bl = sorted(B)
    third = [set(Bl[j::3]) for j in range(3)]
    cents = []
    reps = list(petals)
    Z = set()
    RXs = sorted(R[X])
    for j in range(3):
        need = Z & R[X]
        G = set(need)
        m = max(tau[X] + 1, len(need))
        for x in RXs:
            if len(G) >= m:
                break
            G.add(x)
        S = G | (B - third[j])
        reqs.append(S)
        C = ask(S)
        if C is None:
            return dict(replies=reps, requests=reqs, flags=flags, trivial=True)
        if classify(C) != Y:
            flags.append("centre %d not class Y" % j)
        cents.append(C)
        reps.append(C)
        Z |= (C & U)
    for a in range(3):
        for b in range(a + 1, 3):
            if cents[a] & cents[b] & U:
                flags.append("traces of centres %d,%d intersect on U" % (a, b))
    return dict(replies=reps, requests=reqs, flags=flags, X=X)


def make_fam(k, T, tx, ty, pool=0, slack=0):
    t = Fr(T, k); th = (6 * t - 2) / 5
    rho = []
    for tc in (tx, ty):
        r = math.ceil(k - tc - th * k) - 1 - slack
        rho.append(max(r, 0))
    nx = tx + k - rho[0]
    ny = ty + k - rho[1]
    fam = Family(k, nx, ny, rho, pool)
    return fam


if __name__ == "__main__":
    games = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    cases = []
    # (k,T,tx,ty,pool)
    for (k, T) in [(100, 75), (151, 112), (200, 150), (150, 115)]:
        for (tx, ty) in [(T // 2, T - T // 2 + 1), (T // 2 + 1, T // 2 + 1), (T // 2 - 5, T // 2 + 7), (T // 2 - 1, T // 2 + 3),
                         (T // 2 - 20, T // 2 + 25), (T // 2 + 10, T // 2 + 4), (T // 3, T - T // 3 + 2)]:
            if tx + ty <= T:
                continue
            for pool in (0, 20):
                cases.append((k, T, tx, ty, pool))
    for (k, T, tx, ty, pool) in cases:
        fam = make_fam(k, T, tx, ty, pool)
        th = (6 * Fr(T, k) - 2) / 5
        cc = [fam.cmin(0), fam.cmin(1)]
        if min(cc) <= th * k:
            print("skip (c<=theta)", k, T, tx, ty); continue
        st = run_search(fam, ap_strategy, T, games, seed=k * 7 + tx)
        print("k,T", k, T, "tauX,tauY", tx, ty, "rho", fam.rho, "n", fam.n, "pool", pool, "c", cc, "theta*k", float(th * k),
              "| maxreq", st['maxreq'], "viol", st['budget_viol'], "loses", st['loses'], "wins", st['wins'], "games", st['games'],
              "flags", sorted(set(st['flags']))[:3]); sys.stdout.flush()
