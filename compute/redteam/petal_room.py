"""RED TEAM §6: how much room a petal certificate needs (exact, SAT).

Question A (three_centres configuration): do there exist k-subsets P1..P4 (petals, empty common intersection,
union U) and C1, C2, C3 of an N-set with Ci ∩ Cj ∩ U = empty for i != j?        Hand claim: iff N >= 17k/9 (reals);
integer form: iff exists u >= ceil(4k/3) with 3k <= u + 3(N - u)  i.e.  N >= k + ceil(2*ceil(4k/3)/3).
Question B (5+2 closure of NEW_PATHS Cor. 6.2): four petals as above and one more k-set G with |U| + |G ∩ U| <= 2T.
Hand claim: iff N >= k + 2*ceil(4k/3) - 2T  (and N >= ceil(4k/3)).
Both are decided by SAT (python-sat, exact) and compared with the formulas.
Usage: py petal_room.py kmax"""
import sys, math, itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool

def base(k, N, nsets):
    pool = IDPool(); cl = []
    x = [[pool.id(("x", s, v)) for v in range(N)] for s in range(nsets)]
    for s in range(nsets):
        enc = CardEnc.equals(lits=x[s], bound=k, vpool=pool, encoding=EncType.seqcounter); cl += enc.clauses
    for v in range(N): cl.append([-x[s][v] for s in range(4)])          # petals: no common point
    u = [pool.id(("u", v)) for v in range(N)]
    for v in range(N):
        cl.append([-u[v]] + [x[s][v] for s in range(4)])
        for s in range(4): cl.append([u[v], -x[s][v]])
    # symmetry breaking: points sorted so that U is a prefix
    for v in range(N - 1): cl.append([u[v], -u[v + 1]])
    return pool, cl, x, u

def exists_A(k, N):
    pool, cl, x, u = base(k, N, 7)
    for i, j in itertools.combinations(range(4, 7), 2):
        for v in range(N): cl.append([-x[i][v], -x[j][v], -u[v]])
    with Cadical153(bootstrap_with=cl) as s: return s.solve()

def exists_B(k, N, T):
    pool, cl, x, u = base(k, N, 5)
    g = [pool.id(("g", v)) for v in range(N)]                         # g = G ∩ U
    for v in range(N):
        cl.append([-g[v], x[4][v]]); cl.append([-g[v], u[v]]); cl.append([g[v], -x[4][v], -u[v]])
    enc = CardEnc.atmost(lits=u + g, bound=2 * T, vpool=pool, encoding=EncType.seqcounter); cl += enc.clauses
    with Cadical153(bootstrap_with=cl) as s: return s.solve()

if __name__ == "__main__":
    kmax = int(sys.argv[1]); bad = 0
    for k in range(3, kmax + 1):
        u0 = math.ceil(4 * k / 3)
        fA = k + math.ceil(2 * u0 / 3)
        got = [N for N in range(k + 1, 2 * k + 3) if exists_A(k, N)]
        nA = min(got) if got else None
        ok = (nA == fA) and got == list(range(nA, 2 * k + 3))
        bad += not ok
        print(f"k={k}: three_centres configuration exists iff N >= {nA}   formula k+ceil(2*ceil(4k/3)/3) = {fA}   17k/9 = {17*k/9:.2f}   {'OK' if ok else 'MISMATCH'}", flush=True)
        for T in sorted({math.ceil(3 * k / 4), math.ceil(3 * k / 4) + 1, k - 1}):
            if not (k / 2 < T < k): continue
            fB = max(u0, k + 2 * u0 - 2 * T)
            gotB = [N for N in range(k + 1, 2 * k + 4) if exists_B(k, N, T)]
            nB = min(gotB) if gotB else None
            okB = nB == fB or (nB is None and fB > 2 * k + 3)
            bad += not okB
            print(f"      T={T}: 5+2 closable configuration exists iff N >= {nB}   formula max(ceil(4k/3), k+2ceil(4k/3)-2T) = {fB}   (k+T = {k+T}; 11k/3-2T = {11*k/3-2*T:.2f})   {'OK' if okB else 'MISMATCH'}", flush=True)
    print("mismatches:", bad)
