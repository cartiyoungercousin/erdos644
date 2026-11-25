r"""Driver: all splits into q nonempty cells, n from k+T to nmax, target tau > T.
usage: run_cells.py k T q nmax outdir [procs] [time_limit]
Writes outdir/k{k}_T{T}_q{q}.jsonl (one line per instance, cuts included = certificate).
Prints any SEVEN_FREE instance immediately (with T = floor((3k+5)/4) that is a RECORD candidate)."""
import json, os, sys, time
from multiprocessing import Pool
import cells


def work(args):
    a, k, T, tl = args
    return cells.solve_instance(a, k, T, time_limit=tl)


if __name__ == '__main__':
    k, T, q, nmax = map(int, sys.argv[1:5]); outdir = sys.argv[5]
    procs = int(sys.argv[6]) if len(sys.argv) > 6 else 3
    tl = float(sys.argv[7]) if len(sys.argv) > 7 else 1800.0
    os.makedirs(outdir, exist_ok=True)
    fn = os.path.join(outdir, f"k{k}_T{T}_q{q}.jsonl")
    done = set()
    if os.path.exists(fn):
        for line in open(fn):
            r = json.loads(line); done.add(tuple(r['a']))
    jobs = [(a, k, T, tl) for n in range(k + T, nmax + 1) for a in cells.splits(n, q) if a not in done]
    jobs.sort(key=lambda j: sum(j[0]))
    print(f"k={k} T={T} q={q} n<={nmax}: {len(jobs)} instances ({len(done)} already done)", flush=True)
    t0 = time.time(); cnt = {}
    with Pool(procs) as P, open(fn, 'a') as f:
        for r in P.imap_unordered(work, jobs):
            f.write(json.dumps(r) + '\n'); f.flush()
            cnt[r['status']] = cnt.get(r['status'], 0) + 1
            if r['status'] not in ('UNSAT', 'TRIVIAL'):
                print('**', r['status'], r['a'], 'tau', r.get('tau'), 'J', r.get('J'), flush=True)
    print('done', cnt, f"{time.time() - t0:.0f}s", flush=True)
