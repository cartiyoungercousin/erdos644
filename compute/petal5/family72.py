"""Family test (PETAL §26.1): does the fixed pooled family H have property (7,2)?  SAT search for seven members with
no 2-point cover, with class pattern (4 of X, 3 of Y) or free.  python-sat (CaDiCaL), cardinality by CardEnc.
Usage: py family72.py k nA nF dA dF m [pool_only 0/1] [pattern free|43]
"""
import sys, itertools, time, os
EXACT_POOL = os.environ.get('EXACT_POOL') == '1'
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
sys.path.insert(0, __import__("os").path.dirname(__file__))
from pool_strip import Fam, two_cover, tau_profile


def sat72(F, pattern="43", leak_in_pool=False, timeout=None):
    k, N = F.k, F.N
    vp = IDPool()
    x = lambda j, p: vp.id(("x", j, p))
    cnf = CNF()
    cls = []
    if pattern == "43":
        cls = [0, 0, 0, 0, 1, 1, 1]
    for j in range(7):
        lits = [x(j, p) for p in range(N)]
        for cl in CardEnc.equals(lits, k, vpool=vp, encoding=EncType.seqcounter).clauses:
            cnf.append(cl)
        if cls:
            c = cls[j]
            own = [x(j, p) for p in sorted(F.R[c])]
            for cl in CardEnc.atleast(own, k - F.d[c], vpool=vp, encoding=EncType.seqcounter).clauses:
                cnf.append(cl)
            if F.po or leak_in_pool:  # forbid cross-arena leak
                for p in sorted(F.R[1 - c]):
                    cnf.append([-x(j, p)])
            if EXACT_POOL:  # subfamily: exactly d_c points in the pool
                for cl in CardEnc.equals([x(j, p) for p in sorted(F.R[2])], F.d[c], vpool=vp, encoding=EncType.seqcounter).clauses:
                    cnf.append(cl)
        else:
            raise NotImplementedError
    # distinct members: E_j has a point outside E_j' for j < j'
    for j in range(7):
        for jj in range(j + 1, 7):
            ds = []
            for p in range(N):
                dv = vp.id(("d", j, jj, p))
                cnf.append([-dv, x(j, p)]); cnf.append([-dv, -x(jj, p)])
                ds.append(dv)
            cnf.append(ds)
    # symmetry breaking (light): order petals among themselves by lexicographic first point is skipped; instead fix
    # nothing -- instances are small.
    for p in range(N):
        for q in range(p, N):
            ys = []
            for j in range(7):
                y = vp.id(("y", j, p, q))
                cnf.append([-y, -x(j, p)])
                cnf.append([-y, -x(j, q)])
                ys.append(y)
            cnf.append(ys)
    t0 = time.time()
    with Solver(name="cadical153", bootstrap_with=cnf.clauses) as s:
        ok = s.solve()
        if not ok:
            return None, time.time() - t0
        model = set(l for l in s.get_model() if l > 0)
    sets = [set(p for p in range(N) if x(j, p) in model) for j in range(7)]
    return sets, time.time() - t0


if __name__ == "__main__":
    a = list(map(int, sys.argv[1:7]))
    po = len(sys.argv) > 7 and sys.argv[7] == "1"
    F = Fam(*a, pool_only=po)
    tau = tau_profile(F)
    print("H(k=%d,nA=%d,nF=%d,dA=%d,dF=%d,m=%d,pool_only=%s): tau exact = %d (formula %d)"
          % (*a, po, tau, F.tau_c(0) + F.tau_c(1)))
    sets, dt = sat72(F, "43", leak_in_pool=True)
    if sets is None:
        print("  SAT (4A+3F, leaks only in own arena/pool): UNSAT", "%.1fs" % dt)
    else:
        assert all(len(E) == F.k for E in sets)
        cl = [F.classes(E) for E in sets]
        print("  SAT (4A+3F, leaks only in own arena/pool): seven members found %.1fs; classes %s; brute-force 2-cover: %s"
              % (dt, cl, two_cover(sets)))
        print("  pool points used:", sorted(set().union(*sets) & F.R[2]))
        for E in sets:
            print("   ", [len(E & F.R[r]) for r in range(3)], sorted(E))
