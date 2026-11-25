r"""FANO-SUFFICIENCY test.  Re-runs the CEGAR of cells.py, but every proposed (minimised, covering) J is first
searched for a FANO-type good seven (co-types restricted to the up-closure of the lines of a fixed Fano plane on
the member labels [7]; this is exactly the brief's criterion "every line l has j in J with j <= sum_{p not in l} x_p",
in exact form).  Only if none exists is the all-127-types search run.  A J with a good seven but NO Fano-type
seven is recorded ('nonfano_only').  Every examined J has tau > T.
usage: fano_suff.py k T q nmin nmax outdir [procs]   -> outdir/fano_k{k}_T{T}_q{q}.jsonl"""
import json, os, sys, time
from multiprocessing import Pool
import cells

LINES = [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5), (1, 4, 6), (2, 3, 6), (2, 4, 5)]
LM = [sum(1 << e for e in l) for l in LINES]
UPFANO = [S for S in range(1, 128) if any(S & L == L for L in LM)]     # 64 sets, intersecting


def run(args):
    a, k, T = args
    from pysat.solvers import Cadical153
    U = cells.universe(a, k); covers = cells.cover_sets(a, k, T, U)
    rec = dict(a=list(a), k=k, T=T, n=sum(a), examined=0, fano=0, nonfano_only=[], status=None, cuts=[])
    if covers is None:
        rec['status'] = 'TRIVIAL'; return rec
    sat = Cadical153()
    for c in covers:
        sat.add_clause([t + 1 for t in sorted(c)])
    nv = len(U); boxvar = {}
    while True:
        if not sat.solve():
            rec['status'] = 'UNSAT'; break
        pos = set(l for l in sat.get_model() if l > 0)
        J = cells.minimize_J({t for t in range(len(U)) if t + 1 in pos}, covers)
        Jl = [U[t] for t in sorted(J)]
        rec['examined'] += 1
        st, xs = cells.find_seven(a, k, Jl, 600, types=UPFANO)
        if st == 'FOUND':
            rec['fano'] += 1
        else:
            st, xs = cells.find_seven(a, k, Jl, 1800)
            if st == 'FOUND':
                rec['nonfano_only'].append(dict(J=[list(j) for j in Jl], tau=cells.tau_of(a, k, Jl),
                                                fano_status=st, x={str(i): {str(S): c for S, c in xs[i].items()} for i in xs}))
            elif st == 'NONE':
                rec['status'] = 'SEVEN_FREE'; rec['J'] = [list(j) for j in Jl]; rec['tau'] = cells.tau_of(a, k, Jl); break
            else:
                rec['status'] = 'UNKNOWN'; break
        xs = cells.shrink(xs); A = cells.check_seven_config(a, k, xs); lits = []
        for Am in A:
            box = frozenset(t for t, j in enumerate(U) if cells.leq(j, Am))
            if box not in boxvar:
                nv += 1; boxvar[box] = nv
                for t in box:
                    sat.add_clause([-nv, -(t + 1)])
            lits.append(boxvar[box])
        sat.add_clause(sorted(set(lits)))
        rec['cuts'].append({str(i): {str(S): c for S, c in xs[i].items()} for i in xs})
    sat.delete()
    return rec


if __name__ == '__main__':
    k, T, q, nmin, nmax = map(int, sys.argv[1:6]); outdir = sys.argv[6]
    procs = int(sys.argv[7]) if len(sys.argv) > 7 else 3
    jobs = [(a, k, T) for n in range(max(nmin, k + T), nmax + 1) for a in cells.splits(n, q)]
    fn = os.path.join(outdir, f"fano_k{k}_T{T}_q{q}.jsonl")
    tot = dict(examined=0, fano=0, nonfano=0, hi_examined=0, free=0)
    with Pool(procs) as P, open(fn, 'w') as f:
        for r in P.imap_unordered(run, jobs):
            f.write(json.dumps(r) + '\n'); f.flush()
            tot['examined'] += r['examined']; tot['fano'] += r['fano']; tot['nonfano'] += len(r['nonfano_only'])
            tot['free'] += r['status'] == 'SEVEN_FREE'
            if 6 * r['n'] >= 11 * k: tot['hi_examined'] += r['examined']
            if r['nonfano_only']:
                print('** NON-FANO-ONLY', r['a'], [(e['tau'], [j[0] for j in e['J']]) for e in r['nonfano_only']], flush=True)
            if r['status'] not in ('UNSAT', 'TRIVIAL', 'SEVEN_FREE'):
                print('**', r['status'], r['a'], flush=True)
    print(f"k={k} T={T} q={q} n={nmin}..{nmax}:", tot, flush=True)
