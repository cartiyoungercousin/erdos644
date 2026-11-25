r"""Method C: SAT for '(7,2) and tau >= T' on a fixed ground set of n points, k-uniform, CEGAR.
Variables x_S (k-sets).  tau >= T: for every (T-1)-set X, some member lies in V\X.
(7,2): lazy.  For a model H, (a) look for a Lemma 2 colouring (heuristic), add its clause: OR_l u_l, u_l -> no member inside R_l;
(b) otherwise run the exact DFS cover check; a non-Fano cover gives a blocking clause on its seven members.
When the exact check says (7,2), the model is a genuine family.  Random seeds: random initial colourings and solver phases."""
import sys, time, random, itertools, json
from common import *
from fano import *
from pc72 import find_cover_dfs
from pysat.solvers import Solver
def run(n, k, T, seed, tlimit=900, ncol0=300, log=print):
    rng = random.Random(seed); S = sets_of_size(n, k); idx = {int(s): i + 1 for i, s in enumerate(S)}; nv = len(S)
    top = [nv]
    def new(): top[0] += 1; return top[0]
    solver = Solver(name='cadical153')
    full = (1 << n) - 1
    # tau >= T
    for X in itertools.combinations(range(n), T - 1):
        comp = full ^ sum(1 << v for v in X)
        solver.add_clause([i for s, i in idx.items() if s & ~comp == 0])
    sub_inside = {}
    def colour_clause(chi):
        us = []
        for L in line_masks(chi, n):
            R = full ^ L; u = new(); us.append(u)
            for s, i in idx.items():
                if s & L == 0: solver.add_clause([-u, -i])
        solver.add_clause(us)
    for _ in range(ncol0):
        perm = list(range(n)); rng.shuffle(perm); chi = [0] * n
        for pos, v in enumerate(perm): chi[v] = pos % 7
        colour_clause(chi)
    t0 = time.time(); it = 0; nblock = 0; ncol = ncol0
    while time.time() - t0 < tlimit:
        it += 1
        if not solver.solve(): return None, dict(status='UNSAT', iters=it, secs=time.time() - t0)
        mo = solver.get_model(); H = S[[i for i in range(nv) if mo[i] > 0]]
        chi = find_fano(H, n, rng, tries=10)
        if chi is not None: colour_clause(chi); ncol += 1; continue
        try: cov = find_cover_dfs(H, n, 7, limit=50_000_000)
        except RuntimeError: log('dfs limit, family', len(H)); return H, dict(status='UNCERTIFIED', iters=it)
        if cov is None: return H, dict(status='SAT-certified', iters=it, secs=time.time() - t0, colourings=ncol, blocks=nblock)
        solver.add_clause([-idx[int(H[m])] for m in cov]); nblock += 1
        if it % 50 == 0: log('it', it, 'members', len(H), 'col', ncol, 'blocks', nblock, round(time.time() - t0))
    return None, dict(status='TIMEOUT', iters=it)
if __name__ == '__main__':
    n, k, T, seed = map(int, sys.argv[1:5]); tl = float(sys.argv[5]) if len(sys.argv) > 5 else 900
    H, info = run(n, k, T, seed, tl, log=lambda *a: print(*a, flush=True)); print(info, flush=True)
    if H is not None:
        save_family(f'sat_n{n}_k{k}_T{T}_s{seed}', H, n, dict(method='sat', k=k, T=T, seed=seed))
        print('saved', len(H), 'tau', tau_ilp(H, n))
