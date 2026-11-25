r"""Methods B and D: tau-constrained top-down removal ("local search maximising tau under (7,2)").
Start from a superset family (complete K_n^(k), a random density-p family, or FKW plus e random extra sets, or any file).
Repeat: find a Lemma 2 colouring giving a Fano-type seven (heuristic); remove ONE of its members, chosen at random among those whose
removal keeps tau >= T (every (T-1)-set X still has a member disjoint from it; tracked by counters).  If no member of any colouring
found is removable, stop ('stuck').  When no colouring is found the family is (7,2) up to the heuristic; analyze.py then certifies it
EXACTLY (DFS/SAT/ILP) and recomputes tau by ILP.  Output family is saved with meta."""
import sys, time, random, itertools
from common import *
from fano import *
def topdown(n, k, T, seed, start, tlimit=600, log=print, nfail=60):
    rng = random.Random(seed); S = sets_of_size(n, k); pos = {int(s): i for i, s in enumerate(S)}
    alive = np.zeros(len(S), bool)
    for s in start: alive[pos[int(s)]] = True
    full = (1 << n) - 1
    X = np.array([sum(1 << v for v in c) for c in itertools.combinations(range(n), T - 1)], dtype=np.int64)
    # cnt[X] = number of alive members disjoint from X
    cnt = np.zeros(len(X), np.int32)
    for a in range(0, len(S), 2048):
        blk = S[a:a + 2048]; al = alive[a:a + 2048]
        cnt += (((X[:, None] & blk[None, :]) == 0) & al[None, :]).sum(axis=1).astype(np.int32)
    if (cnt == 0).any(): return None, dict(status='start has tau<T')
    t0 = time.time(); removed = 0; fails = 0; ilpc = [0]
    while time.time() - t0 < tlimit:
        M = S[alive]; chi = find_fano_fast(M, n, rng)
        if chi is None:
            ok72, v, cover = is_72_ilp(M, n, tl=600)
            if ok72 is None: return M, dict(status='ilp-timeout', removed=removed)
            if ok72: return M, dict(status='ilp-certified', removed=removed, secs=round(time.time() - t0, 1))
            cl = [int(M[i]) for i in cover]; rng.shuffle(cl); ok = None
            for m in cl:
                if (cnt[(X & m) == 0] >= 2).all(): ok = m; break
            if ok is None:
                fails += 1
                if fails >= nfail: return M, dict(status='stuck', removed=removed, secs=round(time.time() - t0, 1))
                continue
            alive[pos[ok]] = False; cnt[(X & ok) == 0] -= 1; removed += 1; ilpc[0] += 1; continue
        done = False
        for _ in range(60):   # keep using this colouring while it is still bad
            if any(len(c) == 0 for c in colouring_members(M, chi, n)): break
            order = []
            for L in line_masks(chi, n):
                order += [int(m) for m in M[(M & L) == 0]]
            rng.shuffle(order); ok = None
            for m in order[:80]:
                sel = (X & m) == 0
                if (cnt[sel] >= 2).all(): ok = m; break
            if ok is None: break
            alive[pos[ok]] = False; cnt[(X & ok) == 0] -= 1; removed += 1; done = True
            M = S[alive]
        if not done:
            fails += 1
            if fails >= nfail: return M, dict(status='stuck', removed=removed, secs=round(time.time() - t0, 1))
        else: fails = 0
    return S[alive], dict(status='timeout', removed=removed)
def colour_cands(M, chi, n, rng): return None
def make_start(kind, n, k, rng, p=None, e=None):
    S = sets_of_size(n, k)
    if kind == 'complete': return S
    if kind == 'random': return S[np.array([rng.random() < p for _ in range(len(S))])]
    if kind == 'fkw':
        nx = n - (n // 2 if False else 0); X = (1 << (4 * (n // 7))) - 1
        F = S[(pc(S & X) & 1) == 1]; rest = S[(pc(S & X) & 1) == 0]
        ex = rest[np.array([rng.random() < e for _ in range(len(rest))])]
        return np.concatenate([F, ex])
if __name__ == '__main__':
    kind, n, k, T, seed = sys.argv[1], *map(int, sys.argv[2:6]); par = float(sys.argv[6]) if len(sys.argv) > 6 else None
    tl = float(sys.argv[7]) if len(sys.argv) > 7 else 600; rng = random.Random(seed)
    start = make_start(kind, n, k, rng, p=par, e=par)
    H, info = topdown(n, k, T, seed, start, tl, log=lambda *a: print(*a, flush=True)); print(info, flush=True)
    if H is not None and len(H):
        name = f'td_{kind}{"" if par is None else par}_n{n}_k{k}_T{T}_s{seed}'
        save_family(name, H, n, dict(method='topdown-' + kind, k=k, T=T, seed=seed, par=par, info=info, start=int(len(start))))
        print('saved', name, len(H), 'tau', tau_ilp(H, n), flush=True)
