r"""CORE 113: the core9 two-class greedy template (two_ground_sat.py / escape_check.py) at TRUE window instances.
Rule: class c in {asc, desc}; reply to a T-set S of class c = S + the first omega points of V∖S in order c (omega = n-k-T).
SAT (CaDiCaL) on the class of every T-set; m_K = 'K is a member'. Lazy cuts:
  - every (Sigma)(b) pencil (three members, union V, triple intersection >= n - 2T) found by pencil_find.js
    in the current family -> clause not(m_K1 and m_K2 and m_K3)   [pencil_find is exhaustive when it says so];
  - when the family is pencil-free (exhaustive check), a good seven found by local search (gs_search.js) -> clause.
Terminates with UNSAT (exact: every selector for these two orders has a pencil or one of the logged sevens), or with a
pencil-free family in which local search finds no good seven (heuristic), or at the time limit.
Usage: py -3.14 tg_window.py k T n [timelimit_s]"""
import itertools, sys, time, subprocess, os
from pysat.solvers import Cadical153
k, T, n = map(int, sys.argv[1:4]); tl = float(sys.argv[4]) if len(sys.argv) > 4 else 2400
maxcut = int(sys.argv[5]) if len(sys.argv) > 5 else 20000
import random
mode = sys.argv[6] if len(sys.argv) > 6 else 'rev'   # rev | randR:seed  (R random orders)
om = n - k - T
if mode == 'rev': orders = [list(range(n)), list(range(n - 1, -1, -1))]
else:
    R_, sd = mode[4:].split(':'); rng = random.Random(int(sd)); orders = [rng.sample(range(n), n) for _ in range(int(R_))]
here = os.path.dirname(os.path.abspath(__file__)); famf = None
famf = os.path.join(here, f'logs/tgw_fam_{k}_{T}_{n}_{mode.replace(":", "s")}.txt')
t0 = time.time(); s = Cadical153(); nv = 0; mem = {}; req = []
def mv(K):
    global nv
    if K not in mem: nv += 1; mem[K] = nv
    return mem[K]
for S in itertools.combinations(range(n), T):
    ms = 0
    for x in S: ms |= 1 << x
    Ks = []
    for o in orders:
        K = ms; cnt = 0
        for x in o:
            if not (ms >> x) & 1:
                K |= 1 << x; cnt += 1
                if cnt == om: break
        Ks.append(K)
    vs = []
    for K in Ks: nv += 1; vs.append(nv); s.add_clause([-nv, mv(K)])
    s.add_clause(vs); req.append((vs, Ks))
print(f"k={k} T={T} n={n} omega={om} orders={mode}: {len(req)} requests, {len(mem)} reachable co-edges ({time.time()-t0:.0f}s)", flush=True)
rnd = 0; npen = 0; nsev = 0
while True:
    rnd += 1
    if not s.solve():
        print(f"UNSAT after {rnd-1} rounds, {npen} pencil cuts, {nsev} good-seven cuts: every selector for these orders has a "
              f"pencil or one of the logged sevens [computed exact] ({time.time()-t0:.0f}s)", flush=True); break
    pos = set(v for v in s.get_model() if v > 0)
    fam = sorted(set(Ks[next(i for i, v in enumerate(vs) if v in pos)] for vs, Ks in req))
    open(famf, 'w').write(' '.join(map(str, fam)))
    r = subprocess.run(['node', os.path.join(here, 'pencil_find.js'), famf, str(n), str(k), str(T), str(maxcut)], capture_output=True, text=True)
    lines = r.stdout.split('\n'); pens = [tuple(map(int, l.split()[1:])) for l in lines if l.startswith('P ')]
    done = next(l for l in lines if l.startswith('DONE'))
    for P in pens: s.add_clause([-mem[K] for K in P])
    npen += len(pens)
    if pens:
        print(f"  round {rnd}: family {len(fam)}, {len(pens)} pencils cut ({done}) ({time.time()-t0:.0f}s)", flush=True)
    else:
        g = subprocess.run(['node', os.path.join(here, 'gs_search.js'), famf, str(n), '40', '300', str(rnd)], capture_output=True, text=True).stdout.strip()
        if g.startswith('G'):
            sev = list(map(int, g.split()[1:])); s.add_clause([-mem[K] for K in set(sev)]); nsev += 1
            print(f"  round {rnd}: PENCIL-FREE family of {len(fam)} members (exhaustive); good seven found and cut: {sev}", flush=True)
        else:
            print(f"  round {rnd}: PENCIL-FREE family of {len(fam)} members (exhaustive); local search found NO good seven "
                  f"[heuristic]; family in {famf} ({time.time()-t0:.0f}s)", flush=True); break
    if time.time() - t0 > tl: print(f"TIME LIMIT after {rnd} rounds ({npen} pencil cuts, {nsev} seven cuts)", flush=True); break
