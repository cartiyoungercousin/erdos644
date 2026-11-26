r"""All co-type configurations of a pair-covering of [n] by m blocks of size c (default n=15, m=7, c=7), up to S_m.
A configuration = multiset of n subsets of [m] (the co-types I_x = blocks containing x) that are pairwise intersecting
(every pair covered), each of size >= rmin = ceil((n-1)/(c-1)), and each label i in exactly c of them (|B_i| = c).
Two labelled pair-coverings are isomorphic (under S_n x S_m) iff their configurations are S_m-equivalent, so this is
the list of pair-coverings up to isomorphism; |Aut| and the number of labelled copies n!*m!/... are reported.
Method: DFS over the masks in a fixed order choosing multiplicities; at leaves canonicalise under S_m (min image).
Symmetry pruning: the lexicographically first mask used must be the canonical-first possible, i.e. we require the
configuration to contain mask {0,1,2} (every configuration has a 3-set co-type when E < n), then canonicalise.
Usage: py cotypes15.py [n m c] -> writes logs/cotypes_n_m_c.txt (one configuration per line: masks with multiplicity)
"""
import sys, itertools, time, math
from collections import Counter

n, m, c = (int(a) for a in sys.argv[1:4]) if len(sys.argv) > 3 else (15, 7, 7)
rmin = -(-(n - 1) // (c - 1)); E = m * c - rmin * n
assert E >= 0 and E < n
pc = lambda s: bin(s).count("1")
masks = sorted([s for s in range(1 << m) if pc(s) >= rmin], key=lambda s: (pc(s), s))
first = (1 << rmin) - 1
perms = list(itertools.permutations(range(m)))
permtab = [[sum(1 << p[i] for i in range(m) if s >> i & 1) for s in range(1 << m)] for p in perms]


def canon(cfg):  # cfg: sorted tuple of masks (multiset)
    best = None
    for pt in permtab:
        im = tuple(sorted(pt[s] for s in cfg))
        if best is None or im < best: best = im
    return best


def aut(cfg):
    return sum(1 for pt in permtab if tuple(sorted(pt[s] for s in cfg)) == cfg)


t0 = time.time(); found = set(); leaves = 0
deg0 = [0] * m
cur = []


def dfs(idx, cnt, extra, deg):
    global leaves
    if cnt == n:
        if extra == E:
            leaves += 1
            found.add(canon(tuple(sorted(cur))))
        return
    if idx == len(masks): return
    rem = n - cnt
    s = masks[idx]; e = pc(s) - rmin
    ok = all(s & u for u in cur)
    if ok:
        lab = [i for i in range(m) if s >> i & 1]
        mu = 1
        while mu <= rem and extra + mu * e <= E and all(deg[i] + mu <= c for i in lab):
            for i in lab: deg[i] += mu
            cur.extend([s] * mu)
            dfs(idx + 1, cnt + mu, extra + mu * e, deg)
            del cur[-mu:]
            for i in lab: deg[i] -= mu
            mu += 1
    if idx == 0: return  # mask {0..rmin-1} is forced (WLOG)
    dfs(idx + 1, cnt, extra, deg)


assert masks[0] == first
dfs(0, 0, 0, deg0)
out = sorted(found)
fn = f"logs/cotypes_{n}_{m}_{c}.txt"
tot = 0
with open(fn, "w") as f:
    for cfg in out:
        a = aut(cfg); cnt = Counter(cfg)
        # labelled pair-coverings on [n] (as SETS of m blocks): n! / |Aut of the set system|.
        # Aut(set system) = {(sigma_n, sigma_m)} acting; its order = a * prod(mult!) where a = |stab in S_m of multiset|.
        # number of distinct labelled block-sets = n! * m! / (m! * a * prod mult!) ... see below
        pm = math.prod(math.factorial(v) for v in cnt.values())
        labelled = math.factorial(n) // (a * pm)  # labellings of points / automorphisms (block order forgotten)
        tot += labelled
        f.write(" ".join(f"{s}x{v}" for s, v in sorted(cnt.items())) + f" | aut_m {a} prodmult {pm} labelled {labelled}\n")
print(f"n={n} m={m} c={m} rmin={rmin} E={E}: leaves {leaves}, configurations up to iso {len(out)}, "
      f"labelled pair-coverings (sets of blocks) {tot}  ({time.time()-t0:.1f}s) -> {fn}")
