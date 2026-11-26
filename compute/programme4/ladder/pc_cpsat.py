r"""CP-SAT inner check: does a family F of c-subsets of [n] contain m members covering every pair of [n]?
Model: y[x][i] (point x in block i); each column (y[0][i..], .., y[n-1][i]) is constrained by a TABLE constraint to be
the indicator vector of a member of F (generalised arc consistency on membership); pair coverage via p[x,z,i];
r_x >= ceil((n-1)/(c-1)); block symmetry broken by v_0 > v_1 > ... > v_{m-1}, v_i = sum 2^x y[x][i].
Usage: py pc_cpsat.py famfile n m [workers] [timelimit]
"""
import sys, itertools, time
from ortools.sat.python import cp_model


def solve(fam, n, m, workers=3, tl=None, verbose=True, extra_vars=False):
    c = len(fam[0]); rmin = -(-(n - 1) // (c - 1))
    md = cp_model.CpModel()
    y = [[md.NewBoolVar(f"y{x}_{i}") for i in range(m)] for x in range(n)]
    tuples = [[1 if x in B else 0 for x in range(n)] for B in map(set, fam)]
    for i in range(m):
        md.AddAllowedAssignments([y[x][i] for x in range(n)], tuples)
        md.Add(sum(y[x][i] for x in range(n)) == c)
    for x, z in itertools.combinations(range(n), 2):
        ps = []
        for i in range(m):
            p = md.NewBoolVar(""); ps.append(p)
            md.AddImplication(p, y[x][i]); md.AddImplication(p, y[z][i])
        md.AddBoolOr(ps)
    for x in range(n):
        md.Add(sum(y[x]) >= rmin)
    md.Add(sum(sum(y[x]) for x in range(n)) == m * c)
    v = [sum((1 << (n - 1 - x)) * y[x][i] for x in range(n)) for i in range(m)]
    for i in range(m - 1):
        md.Add(v[i] >= v[i + 1] + 1)
    s = cp_model.CpSolver(); s.parameters.num_workers = workers
    if tl: s.parameters.max_time_in_seconds = tl
    t0 = time.time(); st = s.Solve(md)
    name = s.StatusName(st)
    if verbose: print(f"CP-SAT {name} in {time.time()-t0:.1f}s, branches {s.NumBranches()}", flush=True)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        blocks = [tuple(x for x in range(n) if s.Value(y[x][i])) for i in range(m)]
        fs = set(map(frozenset, fam))
        assert all(frozenset(B) in fs for B in blocks)
        cov = {p for B in blocks for p in itertools.combinations(B, 2)}
        assert len(cov) == n * (n - 1) // 2
        return "SAT", blocks
    return name, None


if __name__ == "__main__":
    fam = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
    n, m = int(sys.argv[2]), int(sys.argv[3])
    w = int(sys.argv[4]) if len(sys.argv) > 4 else 3; tl = float(sys.argv[5]) if len(sys.argv) > 5 else None
    print(f"family {len(fam)} sets of size {len(fam[0])}, n={n}, m={m}", flush=True)
    print(solve(fam, n, m, w, tl))
