"""Independent exhaustive check of notes/MINIMAL_FRAME.md Lemmas 1,3,4 and Cor 5 at tiny sizes.
Usage: py -3.14 minframe.py k T n [cap]
Finds counterexamples ((7,2)-families, tau>T, sets of size 1..k in [n]); enumerates globally
minimum-size ones (up to iso) and many locally-minimal ones; checks lemmas on each."""
import sys, itertools, random
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.examples.rc2 import RC2
from pysat.formula import WCNF


def tau(fam, V):
    V = sorted(V)
    for r in range(0, len(V) + 1):
        for X in itertools.combinations(V, r):
            Xs = set(X)
            if all(Xs & B for B in fam):
                return r
    return len(V) + 1


def has2(fam, V):  # transversal of <=2 points
    V = sorted(V)
    if not fam:
        return True
    for a in V:
        for b in V:
            if all((a in B) or (b in B) for B in fam):
                return True
    return False


def is72(H, V):
    for r in range(1, min(7, len(H)) + 1):
        for sub in itertools.combinations(H, r):
            if not has2(sub, V):
                return False
    return True


def Vof(H):
    return set().union(*H) if H else set()


def is_ce(H, T):
    V = Vof(H)
    return len(H) > 0 and is72(H, V) and tau(H, V) > T


def local_min(H, T):
    """No member removal, no point deletion (size>=2) leaves a counterexample."""
    H = list(H)
    for i, B in enumerate(H):
        G = H[:i] + H[i + 1:]
        if G and is_ce(G, T):
            return False
        if len(B) >= 2:
            for z in B:
                G2 = list(dict.fromkeys(H[:i] + [B - {z}] + H[i + 1:]))
                if is_ce(G2, T):
                    return False
    return True


def uncov(Ks, V):
    """U(K_1..K_m) per FABLE_C Def 2.1."""
    I = {x: frozenset(i for i, K in enumerate(Ks) if x in K) for x in V}
    U = set()
    for x in V:
        for y in V:
            if not (I[x] & I[y]):
                U.add(x)
                U.add(y)
    return U


def transv_le2(fam, V):
    return [(a, b) for a in sorted(V) for b in sorted(V) if a <= b and all((a in B) or (b in B) for B in fam)]


def check(H, T):
    """Return list of failure strings (Lemma 3, Lemma 4, Cor 5, antichain/no-dup)."""
    fails = []
    V = Vof(H)
    Hl = list(H)
    if len(set(Hl)) != len(Hl):
        fails.append("duplicate members")
    for i, B in enumerate(Hl):
        for j, C in enumerate(Hl):
            if i != j and B <= C:
                fails.append("non-antichain")
    for i, B in enumerate(Hl):  # Lemma 3
        oth = Hl[:i] + Hl[i + 1:]
        ok = False
        K = sorted(V - B)
        for r in range(0, T + 1):
            for S in itertools.combinations(K, r):
                if all(set(S) & C for C in oth):
                    ok = True
                    break
            if ok:
                break
        if not ok:
            fails.append(f"L3 fail B={sorted(B)}")
    cos = [frozenset(V - B) for B in Hl]
    nwit = 0
    for i, B in enumerate(Hl):  # Lemma 4 + Cor 5
        oth_idx = [j for j in range(len(Hl)) if j != i]
        for z in B:
            if len(B) < 2:
                continue
            wit = 0
            for r in range(0, 7):
                for sub in itertools.combinations(oth_idx, r):
                    fam1 = [B - {z}] + [Hl[j] for j in sub]
                    if has2(fam1, V):
                        continue  # (i) fails
                    fam2 = [B] + [Hl[j] for j in sub]
                    tr = transv_le2(fam2, V)
                    if not all((set(x) & B) == {z} for x in tr):
                        continue  # (ii) fails
                    wit += 1
                    Ks = [cos[j] for j in sub]
                    U = uncov(Ks, V)
                    if len(Ks) > 6:
                        fails.append("C5 >6")
                    if not (z in U):
                        fails.append(f"C5 z notin U B={sorted(B)} z={z}")
                    if not (U <= cos[i] | {z}):
                        fails.append(f"C5 U not subset K+z B={sorted(B)} z={z}")
                    if any(U <= Kp for Kp in cos):
                        fails.append("C5 U inside some co-edge")
                    if len(U) < T + 1:
                        fails.append("C5 |U|<T+1")
            if wit == 0:
                fails.append(f"L4 no witness B={sorted(B)} z={z}")
            nwit += wit
    return fails


def canon(H, n):
    best = None
    for p in itertools.permutations(range(n)):
        c = tuple(sorted(tuple(sorted(p[x] for x in B)) for B in H))
        if best is None or c < best:
            best = c
    return best


def build(n, k):
    subs = [frozenset(c) for r in range(1, k + 1) for c in itertools.combinations(range(n), r)]
    var = {S: i + 1 for i, S in enumerate(subs)}
    return subs, var


def static_clauses(n, k, T):
    subs, var = build(n, k)
    hard = []
    for X in itertools.combinations(range(n), T):
        Xs = set(X)
        hard.append([var[S] for S in subs if not (S & Xs)])
    return subs, var, hard


def bad_seven(F, V):
    """indices of <=7 members of F with no 2-transversal (minimised), or None."""
    m = len(F)
    if m == 0:
        return None
    Vl = sorted(V)
    s = Cadical153()
    for a in Vl:
        for b in Vl:
            if a <= b:
                s.add_clause([i + 1 for i, B in enumerate(F) if a not in B and b not in B])
    card = CardEnc.atmost(lits=list(range(1, m + 1)), bound=7, top_id=m, encoding=EncType.seqcounter)
    for c in card.clauses:
        s.add_clause(c)
    if not s.solve():
        return None
    mod = s.get_model()
    sel = [i for i in range(m) if mod[i] > 0]
    for i in list(sel):
        t = [j for j in sel if j != i]
        if not has2([F[j] for j in t], V):
            sel = t
    return sel


def find_min_cost(n, k, T):
    subs, var, hard = static_clauses(n, k, T)
    lazy = []
    while True:
        w = WCNF()
        for c in hard + lazy:
            w.append(c)
        for S in subs:
            w.append([-var[S]], weight=len(S))
        with RC2(w) as r:
            m = r.compute()
            if m is None:
                return None, subs, var, hard, lazy
            cost = r.cost
        F = [S for S in subs if m[var[S] - 1] > 0]
        bs = bad_seven(F, set(range(n)))
        if bs is None:
            return cost, subs, var, hard, lazy
        lazy.append([-var[F[i]] for i in bs])


def enum_min(n, k, T, cost, subs, var, hard, lazy, cap):
    top = len(subs)
    lits = []
    clauses = list(hard) + list(lazy)
    for S in subs:
        lits.append(var[S])
        for _ in range(len(S) - 1):
            top += 1
            clauses += [[-var[S], top], [var[S], -top]]
            lits.append(top)
    card = CardEnc.atmost(lits=lits, bound=cost, top_id=top, encoding=EncType.totalizer)
    s = Cadical153()
    for c in clauses + card.clauses:
        s.add_clause(c)
    cnt = 0
    while cnt < cap and s.solve():
        m = s.get_model()
        F = [S for S in subs if m[var[S] - 1] > 0]
        bs = bad_seven(F, set(range(n)))
        if bs is not None:
            s.add_clause([-var[F[i]] for i in bs])
            continue
        cnt += 1
        s.add_clause([-var[S] for S in F])
        yield F


def random_ces(n, k, T, trials, seed):
    subs, var, hard = static_clauses(n, k, T)
    rnd = random.Random(seed)
    lazy = []
    out = []
    for _ in range(trials):
        s = Cadical153()
        for c in hard + lazy:
            s.add_clause(c)
        s.set_phases([v if rnd.random() < 0.3 else -v for v in range(1, len(subs) + 1)])
        while s.solve():
            m = s.get_model()
            F = [S for S in subs if m[var[S] - 1] > 0]
            bs = bad_seven(F, set(range(n)))
            if bs is None:
                out.append(F)
                break
            cl = [-var[F[i]] for i in bs]
            lazy.append(cl)
            s.add_clause(cl)
    return out


def reduce_local(H, T, rnd):
    H = list(H)
    changed = True
    while changed:
        changed = False
        moves = []
        for i, B in enumerate(H):
            moves.append(("rm", i, None))
            if len(B) >= 2:
                for z in B:
                    moves.append(("del", i, z))
        rnd.shuffle(moves)
        for kind, i, z in moves:
            if kind == "rm":
                G = H[:i] + H[i + 1:]
            else:
                G = list(dict.fromkeys(H[:i] + [H[i] - {z}] + H[i + 1:]))
            if G and is_ce(G, T):
                H = G
                changed = True
                break
    return H


if __name__ == "__main__":
    k, T, n = map(int, sys.argv[1:4])
    cap = int(sys.argv[4]) if len(sys.argv) > 4 else 200
    cost, subs, var, hard, lazy = find_min_cost(n, k, T)
    print(f"k={k} T={T} n={n}: min ||H|| =", cost)
    stats = {"global": 0, "local": 0, "fails": 0}
    if cost is not None:
        seen = set()
        for F in enum_min(n, k, T, cost, subs, var, hard, lazy, cap):
            c = canon(F, n) if n <= 7 else tuple(sorted(tuple(sorted(B)) for B in F))
            if c in seen:
                continue
            seen.add(c)
            stats["global"] += 1
            assert is_ce(F, T)
            f = check(F, T)
            if f:
                stats["fails"] += 1
                print("FAIL global", sorted(map(sorted, F)), f[:3])
        print("distinct global-minimum counterexamples (iso classes among first", cap, "labelled):", len(seen))
        rnd = random.Random(1)
        ces = random_ces(n, k, T, 25, 1)
        locs = set()
        for F in ces:
            H = reduce_local(F, T, rnd)
            assert local_min(H, T) and is_ce(H, T)
            c = tuple(sorted(tuple(sorted(B)) for B in H))
            if c in locs:
                continue
            locs.add(c)
            stats["local"] += 1
            f = check(H, T)
            if f:
                stats["fails"] += 1
                print("FAIL local", c, f[:3])
        print("distinct locally-minimal counterexamples checked:", len(locs),
              "||H|| values", sorted(sum(len(B) for B in c) for c in locs)[:12])
    print(stats)
