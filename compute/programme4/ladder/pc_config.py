r"""Inner check by configuration: for each isomorphism class of pair-covering of [n] by 7 blocks of size c (the list
from cotypes2.js), decide by CP-SAT whether family F contains a copy.  F contains a good seven iff some class embeds.
Model per class: y[x][i] (point x in block i); each row (y[x][0..6]) equals one of the class's co-types (table
constraint), co-type T used by exactly mult(T) points; each column is a member of F (table constraint).
(The pair-covering and degree conditions are then automatic: the co-types are pairwise intersecting.)
Usage: py pc_config.py famfile n configfile [timelimit_per_class] [workers] [first_class] [last_class]
"""
import sys, time, itertools
from ortools.sat.python import cp_model


def load_configs(fn):
    out = []
    for line in open(fn):
        if not line.strip(): continue
        body = line.split("|")[0].split()
        out.append({int(a): int(b) for a, b in (t.split(":") for t in body)})
    return out


def embed(fam, n, cfg, tl=None, workers=1, hint=None):
    md = cp_model.CpModel(); m = 7
    y = [[md.NewBoolVar("") for i in range(m)] for x in range(n)]
    types = sorted(cfg)
    rows = [[(T >> i) & 1 for i in range(m)] for T in types]
    z = [[md.NewBoolVar("") for _ in types] for x in range(n)]
    for x in range(n):
        md.AddExactlyOne(z[x])
        for t, T in enumerate(types):
            for i in range(m):
                if (T >> i) & 1: md.AddImplication(z[x][t], y[x][i])
                else: md.AddImplication(z[x][t], y[x][i].Not())
        md.AddAllowedAssignments(y[x], rows)
    for t, T in enumerate(types):
        md.Add(sum(z[x][t] for x in range(n)) == cfg[T])
    tup = [[1 if x in B else 0 for x in range(n)] for B in map(set, fam)]
    for i in range(m):
        md.AddAllowedAssignments([y[x][i] for x in range(n)], tup)
    s = cp_model.CpSolver(); s.parameters.num_workers = workers
    if tl: s.parameters.max_time_in_seconds = tl
    st = s.Solve(md)
    if st in (cp_model.OPTIMAL, cp_model.FEASIBLE):
        blocks = [tuple(x for x in range(n) if s.Value(y[x][i])) for i in range(m)]
        return "SAT", blocks, s.WallTime()
    return s.StatusName(st), None, s.WallTime()


def check(blocks, fam, n):
    fs = set(map(frozenset, fam))
    cov = {p for B in blocks for p in itertools.combinations(sorted(B), 2)}
    return all(frozenset(B) in fs for B in blocks) and len(cov) == n * (n - 1) // 2


if __name__ == "__main__":
    fam = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
    n = int(sys.argv[2]); cfgs = load_configs(sys.argv[3])
    tl = float(sys.argv[4]) if len(sys.argv) > 4 else None
    w = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    a = int(sys.argv[6]) if len(sys.argv) > 6 else 0; b = int(sys.argv[7]) if len(sys.argv) > 7 else len(cfgs)
    print(f"family {len(fam)} sets, n={n}, {len(cfgs)} classes; doing {a}..{b-1}, tl={tl}, workers={w}", flush=True)
    t0 = time.time(); undecided = []
    for ci in range(a, b):
        st, bl, wt = embed(fam, n, cfgs[ci], tl, w)
        print(f"class {ci}: {st} ({wt:.1f}s)", flush=True)
        if st == "SAT":
            assert check(bl, fam, n); print("GOOD SEVEN:", bl, flush=True); break
        if st != "INFEASIBLE": undecided.append(ci)
    print(f"done {time.time()-t0:.0f}s; undecided classes: {undecided}", flush=True)
