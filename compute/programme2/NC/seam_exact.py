r"""Seam check for PROGRAMME2_NC.md.  Parity-twisted complete families on W = W1 u W2:
E = { B in (W choose k) : |B n W1| = par (mod 2) } (par None = complete).  Exact (7,2) test in co-edge form:
SAT 'seven members whose complements cover every pair' (CaDiCaL, sequential-counter cardinality), with the redundant
(valid) constraint 'each point lies in >= ceil((n-1)/(n-k-1)) of the seven complements'.  tau by enumeration."""
import sys, itertools, time
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

def fam(k, w1, w2, par):
    n = w1 + w2
    return [B for B in itertools.combinations(range(n), k)
            if par is None or sum(1 for x in B if x < w1) % 2 == par], n

def tau(M, n, k):
    S = [frozenset(B) for B in M]
    for m in range(n + 1):
        for U in itertools.combinations(range(n), n - m):
            U = frozenset(U)
            if not any(B <= U for B in S): return m

def seven(M, n, k):
    """7 slots; slot variables x[s][i] = member i in slot s (exactly one per slot); pair coverage via aux."""
    N = len(M); top = [0]
    def nv(): top[0] += 1; return top[0]
    X = [[nv() for _ in range(N)] for _ in range(7)]
    cl = []
    for s in range(7):
        e = CardEnc.equals(lits=X[s], bound=1, top_id=top[0], encoding=EncType.seqcounter); top[0] = max(top[0], e.nv); cl += e.clauses
    # y[i] = member i used in some slot
    Y = [nv() for _ in range(N)]
    for i in range(N):
        cl.append([-Y[i]] + [X[s][i] for s in range(7)])
    comp = [set(range(n)) - set(B) for B in M]
    for a in range(n):
        for b in range(a + 1, n):
            cl.append([Y[i] for i in range(N) if a in comp[i] and b in comp[i]])
    # symmetry: slots ordered by index (slot s uses member index <= slot s+1's): skip, small enough
    with Solver(name='cadical153', bootstrap_with=cl) as S:
        if not S.solve(): return None
        mdl = set(l for l in S.get_model() if l > 0)
        return [M[i] for i in range(N) if Y[i] in mdl]

def no2t(B7, n):
    return not any(all((a in B) or (b in B) for B in B7) for a in range(n) for b in range(a, n))

if __name__ == '__main__':
    cases = [tuple(None if x == 'N' else int(x) for x in c.split(',')) for c in sys.argv[1:]]
    for (k, w1, w2, par) in cases:
        t0 = time.time(); M, n = fam(k, w1, w2, par); t = tau(M, n, k)
        c = seven(M, n, k)
        print(f"k={k} |W1|={w1} |W2|={w2} par={par} n={n} |H|={len(M)} tau={t} -> "
              + ('(7,2) [UNSAT, exact]' if c is None else f'NOT (7,2), seven verified={no2t(c, n)} ({len(c)} distinct)')
              + f"  {time.time()-t0:.1f}s", flush=True)
