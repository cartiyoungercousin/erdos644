r"""Family builders for PROGRAMME_2 Task 1.  Every builder returns (Family of EDGES, orbits or None).  Co-edge files are complemented."""
import os, sys, glob, itertools, random
import numpy as np
from tau_star import Family, popcount
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))   # .../compute

def allmasks(n): return np.arange(1 << n, dtype=np.int64)

def fkw(m):
    n, k, nx = 7 * m + 1, 4 * m, 4 * m
    a = allmasks(n); pc = popcount(a); px = popcount(a & ((1 << nx) - 1))
    sel = a[(pc == k) & (px % 2 == 1)]
    return Family(n, sel, f'FKW m={m} (n={n},k={k})'), [0 if v < nx else 1 for v in range(n)]

def h1():
    n, nx = 22, 12; a = allmasks(n); pc = popcount(a); px = popcount(a & ((1 << nx) - 1))
    sel = a[(pc == 12) & np.isin(px, [3, 5, 7, 9])]
    extra = [((1 << nx) - 1) & ~(1 << x) for x in range(nx)]
    return Family(n, np.concatenate([sel, extra]), 'H1'), [0 if v < nx else 1 for v in range(n)]

def npy(path, name):
    return Family(22, np.load(path), name), None

def u1(path, name):
    n, nx = 22, 12; G = [int(b) for b in np.load(path)]
    lift = lambda B: B | (1 << (n + next(x for x in range(nx) if not B >> x & 1))) if bin(B).count('1') == 11 else B
    return Family(34, [lift(B) for B in G], name), None

def complete(n, k):
    a = allmasks(n); sel = a[popcount(a) == k]
    return Family(n, sel, f'complete K_{n}^({k})'), [0] * n

def coedge_text(path, n, name):
    cos = [sum(1 << int(x) for x in l.split()) for l in open(path) if l.strip()]
    full = (1 << n) - 1
    return Family(n, [full ^ c for c in cos], name), None

def coedge_masks(path, n, name):
    full = (1 << n) - 1
    return Family(n, [full ^ int(x) for x in open(path).read().split()], name), None

def profile_family(P, nA=18, nY=3, c=11):
    """co-edges = all c-sets with (|K&A|,|K&Y|) in P; edges = complements."""
    n = nA + nY; a = allmasks(n); A = (1 << nA) - 1
    pa = popcount(a & A); py = popcount(a >> nA)
    ok = np.zeros(len(a), bool)
    for (x, y) in P: ok |= (pa == x) & (py == y)
    full = (1 << n) - 1
    return Family(n, full ^ a[ok], f'near-pool (10,8,21) P={P}'), [0] * nA + [1] * nY

def hash_family(kind, R, mode, n, k, T, seed):
    sys.path.insert(0, os.path.join(ROOT, 'core9'))
    import hash_check as hc
    rng = random.Random(seed); RR = R if R else T - k // 2 + 2
    if mode == 'rev': orders = [list(range(n)), list(range(n - 1, -1, -1))] + [rng.sample(range(n), n) for _ in range(RR - 2)]
    else: orders = [rng.sample(range(n), n) for _ in range(RR)]
    rule = hc.Rule(n, k, T, orders, hc.make_selector(kind, n, k, T, RR, rng))
    full = (1 << n) - 1; reps = set()
    for S in itertools.combinations(range(n), T):
        K = rule.reply(frozenset(S)); reps.add(sum(1 << x for x in K))
    return Family(n, [full ^ r for r in reps], f'rule {kind} R={RR} {mode} (k={k},T={T},n={n})'), None
