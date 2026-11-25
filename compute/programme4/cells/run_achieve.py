r"""Achievability scan: target tau > T, n increasing from k+T; for each n all splits into q cells (q = 1, 2 given);
stops after the first n at which some instance is SEVEN_FREE (all instances of that n are finished).
usage: run_achieve.py k T q nmax outdir [procs]"""
import json, os, sys
from multiprocessing import Pool
import cells


def work(args):
    a, k, T = args
    return cells.solve_instance(a, k, T, time_limit=1800)


if __name__ == '__main__':
    k, T, q, nmax = map(int, sys.argv[1:5]); outdir = sys.argv[5]
    procs = int(sys.argv[6]) if len(sys.argv) > 6 else 3
    fn = os.path.join(outdir, f"ach_k{k}_T{T}_q{q}.jsonl")
    with Pool(procs) as P, open(fn, 'a') as f:
        for n in range(k + T, nmax + 1):
            free = []
            for r in P.imap_unordered(work, [(a, k, T) for a in cells.splits(n, q)]):
                f.write(json.dumps(r) + '\n'); f.flush()
                if r['status'] == 'SEVEN_FREE':
                    free.append((r['a'], r['tau'], r['J']))
                elif r['status'] not in ('UNSAT', 'TRIVIAL'):
                    print('**', r['status'], r['a'], flush=True)
            print(f"k={k} T={T} q={q} n={n}: {len(free)} seven-free", flush=True)
            for a, t, J in sorted(free):
                print('   ', a, 'tau', t, 'J(first coords)', [j[0] for j in J], flush=True)
            if free:
                break
