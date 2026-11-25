"""PETAL §40: strided chunk runner for search.py (same model, same exact SAT+CEGAR).
usage: py search_chunk.py k m_max n_lo n_hi min_m start stride residue per_instance_timeout_s
Processes size vectors idx >= start with idx % stride == residue. A per-instance TIMEOUT is logged and skipped
(so the chunk keeps going); TIMEOUT lines must be re-run before the range counts as proved."""
import sys, time
from search import partitions, solve_size

k, m_max, n_lo, n_hi, min_m, start, stride, res = map(int, sys.argv[1:9])
pit = float(sys.argv[9])
c = {12: 7, 16: 9}[k]; T = 3 * k // 4; mu = c - 1
sizes = [tuple(p) for n in range(n_lo, n_hi + 1) for p in partitions(n, m_max, 2 * k) if len(p) >= min_m]
print('k', k, 'c', c, 'mu', mu, 'T', T, 'size vectors', len(sizes), 'start', start, 'stride', stride, 'res', res, flush=True)
stats = {}; t0 = time.time()
for idx in range(start, len(sizes)):
    if idx % stride != res: continue
    s = sizes[idx]; t1 = time.time()
    r = solve_size(list(s), k, c, mu, T, deadline=time.time() + pit)
    st = r['status']; stats[st] = stats.get(st, 0) + 1
    if st in ('HIT', 'TIMEOUT', 'NO_HIT_RANGE_FEASIBLE'):
        print(idx, s, st, {a: b for a, b in r.items() if a not in ('X', 'Y')}, 'X', r.get('X'), 'Y', r.get('Y'),
              '%.1fs' % (time.time() - t1), flush=True)
print('DONE', 'STATS', stats, 'elapsed %.0fs' % (time.time() - t0), flush=True)
