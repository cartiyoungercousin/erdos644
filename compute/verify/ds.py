"""Theorem DS (20.2) verbatim, arena-aware, and DS-b (21.1) blind.  usage: py ds.py"""
import sys, random
from common import *


def ds_strategy(fam, T, ask, eps=1):
    """20.2 verbatim.  Arena 0 = V_A, arena 1 = V_F (here A=region0, F=region1)."""
    k = fam.k
    nA, nF = fam.n
    VA, VF = fam.R[0], fam.R[1]
    half = T // 2  # T even assumed
    reqs, reps, flags = [], [], []
    # chunks of V_A of size half-eps covering V_A
    h = half - eps
    if 4 * h < nA:
        flags.append("chunks cannot cover V_A")
    chunk = []
    for i in range(4):
        st = (i * nA) // 4
        chunk.append({(st + j) % nA for j in range(h)})
    if set().union(*chunk) != VA:
        flags.append("chunks do not cover")
    Fpts = sorted(VF)
    for i in range(4):
        earlier_F = set()
        for E in reps:
            earlier_F |= (E & VF)
        if len(earlier_F) > half + eps:
            flags.append("petal req %d: F-parts %d > t/2+eps" % (i, len(earlier_F)))
        Sf = set(earlier_F)
        for x in Fpts:
            if len(Sf) >= half + eps:
                break
            Sf.add(x)
        S = chunk[i] | Sf
        reqs.append(S)
        E = ask(S)
        if E is None:
            return dict(replies=reps, requests=reqs, flags=flags, trivial=True)
        reps.append(E)
        if len(E & VF) >= k - fam.rho[1] + 0 and len(E & VA) < k - fam.rho[0]:
            flags.append("petal %d has colour F (forcing failed)" % i)
    U = set().union(*reps)
    B = set()
    for E in reps:
        B |= (E & VF)
    Bl = sorted(B)
    third = [set(Bl[j::3]) for j in range(3)]
    cents = []
    Apts = sorted(VA)
    for j in range(3):
        Sb = B - third[j]
        earlier_A = set()
        for C in cents:
            earlier_A |= (C & VA)
        if len(earlier_A) > half + eps:
            flags.append("centre %d: earlier A-parts exceed t/2+eps" % j)
        Sa = set(earlier_A)
        for x in Apts:
            if len(Sa) >= half + eps:
                break
            Sa.add(x)
        S = Sb | Sa
        reqs.append(S)
        C = ask(S)
        if C is None:
            return dict(replies=reps, requests=reqs, flags=flags, trivial=True)
        if len(C & VA) >= k - fam.rho[0] and len(C & VF) < k - fam.rho[1]:
            flags.append("centre %d has colour A (forcing failed)" % j)
        cents.append(C)
        reps.append(C)
    # check pairwise disjoint traces on U
    for a in range(3):
        for b in range(a + 1, 3):
            if cents[a] & cents[b] & U:
                flags.append("traces of centres %d,%d intersect on U" % (a, b))
    return dict(replies=reps, requests=reqs, flags=flags)


def dsb_strategy(fam, T, ask):
    """21.1 blind (14.1): running intersections, classes read from overlap threshold c_thr, forcing 1-c of petal X_a=X_1."""
    k = fam.k
    n = fam.n[0]
    d = fam.rho[0]
    a0 = 2 * (k - d) - n
    c_thr = a0 - 1  # same-class overlap > c_thr, cross <= 2d <= c_thr
    half = T // 2
    reqs, reps, flags = [], [], []
    classes = {}  # label -> list of members
    I = {}
    order = []
    for step in range(7):
        S = set()
        for lab in order:
            Il = sorted(I[lab])
            S |= set(Il[:min(half, len(Il))])
        reqs.append(S)
        E = ask(S)
        if E is None:
            return dict(replies=reps, requests=reqs, flags=flags, trivial=True)
        reps.append(E)
        lab = None
        for l in order:
            if len(E & classes[l][0]) > c_thr:
                lab = l
        if lab is None:
            lab = len(order)
            order.append(lab)
            classes[lab] = [E]
            I[lab] = set(E)
            if len(order) > 2:
                flags.append("third class")
        else:
            classes[lab].append(E)
            I[lab] &= E
        if any(len(m) >= 4 and not I[l] for l, m in classes.items() for _ in [0] if len(m) >= 4):
            break
        if any(len(classes[l]) >= 4 and not I[l] for l in order):
            break
    petals = None
    for l in order:
        if len(classes[l]) >= 4 and not I[l]:
            # first four members have empty intersection? I includes all members; need first four
            P4 = classes[l][:4]
            if not (P4[0] & P4[1] & P4[2] & P4[3]):
                petals = P4
                break
    if petals is None:
        flags.append("no four petals with empty intersection")
        return dict(replies=reps, requests=reqs, flags=flags)
    Xa = petals[0]
    U = set().union(*petals)
    cents = []
    reps = list(petals)
    Z = set()
    for j in range(3):
        need = len(Z & Xa)
        fm = max(k - c_thr, need)
        F = set(sorted(Z & Xa))
        for x in sorted(Xa - F):
            if len(F) >= fm:
                break
            F.add(x)
        S = F | (Z - Xa)
        reqs.append(S)
        C = ask(S)
        if C is None:
            return dict(replies=reps, requests=reqs, flags=flags, trivial=True)
        if len(C & Xa) > c_thr:
            flags.append("forced reply in class X")
        cents.append(C)
        reps.append(C)
        Z |= (C & U)
    for a in range(3):
        for b in range(a + 1, 3):
            if cents[a] & cents[b] & U:
                flags.append("traces intersect")
    return dict(replies=reps, requests=reqs, flags=flags)


if __name__ == "__main__":
    which = sys.argv[1]
    games = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    k, T = 80, 60
    for d in [int(x) for x in sys.argv[3:]] or [6, 8, 9, 10]:
        n = k + T // 2 - d
        fam = Family(k, n, n, [d, d])
        if which == "ds":
            st = run_search(fam, ds_strategy, T, games, seed=d)
        else:
            st = run_search(fam, dsb_strategy, T, games, seed=d)
        print(which, "k,T,d,n", k, T, d, n, {a: b for a, b in st.items() if a != "flags"}, "flags:", sorted(set(st["flags"]))[:4])
        sys.stdout.flush()
