import sys, os, json, time, numpy as np
from tau_star import *; import families as F
HERE = os.path.dirname(os.path.abspath(__file__)); C = F.ROOT
def run(p, tag):
    G = [int(b) for b in np.load(os.path.join(C, 'task3/out', p))]
    fam = U1Family(G, name=tag)
    # self-check: the oracle's cuts are genuine transversals, on random y
    rng = np.random.default_rng(0)
    for _ in range(3):
        y = rng.random(fam.n) * 0.08; v, cuts = fam.oracle(y)
        assert all(fam.check_transversal(M) for M in cuts[:20])
        assert abs(v - min(sum(y[i] for i in range(fam.n) if M >> i & 1) for M in cuts[:1])) < 1e-9
    t = time.time(); tm = round(fam.oracle([1.0] * fam.n)[0])
    r = solve(fam, None, kind='x')
    c1, cphi = classify(r)
    d = dict(group='task3', name=tag, n=fam.n, members=len(fam.masks), tau=tm, tau_b=r['tau_b'], tau_b_frac=frac(r['tau_b']),
             margin=SEVEN_THIRDS - r['tau_b'], max_atom=r['max_atom'], atom_frac=frac(r['max_atom']), phi=r['phi'], uniform_bound=fam.n / tm,
             rich=bool(cphi), rich_opt_y=bool(c1), symmetric=False, oracle='bitset-over-old-points x fresh-subset', cuts=r['cuts'], secs=round(time.time() - t, 1),
             y_fresh=[round(v, 4) for v in r['y'][22:]], y_old_range=[round(min(r['y'][:22]), 4), round(max(r['y'][:22]), 4)])
    print(json.dumps(d), flush=True); open(os.path.join(HERE, 'out', 'results.jsonl'), 'a').write(json.dumps(d) + '\n')
run('gprime_fkw1.npy', 'U1 = pad(gprime_fkw1.npy)')
run('h1min_random_1.npy', 'U1 = pad(h1min_random_1.npy)')
