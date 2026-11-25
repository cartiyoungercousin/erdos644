r"""Second, independent implementation on EXPLICIT families (no profile criteria, no co-types):
members are enumerated as bitmasks; tau by exhaustive T-subsets; a good seven by a SAT search
(choose <= 7 members such that every pair {x,y}, x = y allowed, avoids some chosen member), pysat Glucose4 + CardEnc.
Used (a) to test the criteria (tau) and (seven) in cells.py on random small instances, (b) to re-verify any
record candidate.  usage: brute.py test [trials] [seed]
"""
import itertools, random, sys
from pysat.solvers import Glucose4
from pysat.card import CardEnc, EncType


def members(a, k, J):
    J = set(tuple(j) for j in J)
    n = sum(a); cell = []
    for i, ai in enumerate(a):
        cell += [i] * ai
    out = []
    for B in itertools.combinations(range(n), k):
        prof = [0] * len(a)
        for v in B:
            prof[cell[v]] += 1
        if tuple(prof) in J:
            out.append(sum(1 << v for v in B))
    return out


def tau_brute(n, M):
    for T in range(0, n + 1):
        for U in itertools.combinations(range(n), T):
            u = sum(1 << v for v in U)
            if all(B & u for B in M):
                return T
    return n + 1


def seven_brute(n, M):
    """True iff some <= 7 members have no transversal of size <= 2"""
    if not M:
        return False
    s = Glucose4()
    nv = len(M)
    for x in range(n):
        for y in range(x, n):
            p = (1 << x) | (1 << y)
            cl = [t + 1 for t, B in enumerate(M) if not (B & p)]
            if not cl:
                return False
            s.add_clause(cl)
    enc = CardEnc.atmost(lits=list(range(1, nv + 1)), bound=7, top_id=nv, encoding=EncType.seqcounter)
    for c in enc.clauses:
        s.add_clause(c)
    r = s.solve(); s.delete()
    return r


if __name__ == '__main__' and sys.argv[1] == 'test':
    from cells import tau_of, find_seven, universe
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
    bad = 0; stats = [0, 0]
    for tr in range(trials):
        q = rng.choice([1, 2, 2, 3, 3])
        k = rng.randint(2, 5)
        n = rng.randint(k + 1, min(11, 2 * k + 3))
        if n < q:
            continue
        cuts = sorted(rng.sample(range(1, n), q - 1)); a = tuple(b - c for b, c in zip(cuts + [n], [0] + cuts))
        U = universe(a, k)
        J = [j for j in U if rng.random() < rng.choice([0.4, 0.7, 0.9])]
        if not J:
            continue
        M = members(a, k, J)
        t1, t2 = tau_of(a, k, J), tau_brute(n, M)
        s1 = find_seven(a, k, J, 60)[0] == 'FOUND'; s2 = seven_brute(n, M)
        stats[s2] += 1
        if t1 != t2 or s1 != s2:
            bad += 1; print('MISMATCH', a, k, J, t1, t2, s1, s2)
    print('trials done; mismatches', bad, '; seven-free/with-seven', stats)
