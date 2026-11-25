r"""CORE 55.5, decisive method.  Step 1 [computed exact, family-free]: enumerate every abstract co-type configuration of a
pair-cover of n points by seven c-sets: a multiset of n subsets of [7] (the co-types I_x), pairwise intersecting (x = y
included, so nonempty), every label in exactly c of them.  Reduced up to the action of S_7 on labels.
Step 2 [computed exact]: for each configuration, search for members K_0..K_6 of the family realising it.  Labels are
processed in order and K_j is chosen so that, for every partial pattern p of labels < j, |K_j ∩ region(p)| equals the number
of configuration slots with pattern p that contain j.  This is exactly "the Venn counts of K_0..K_j agree with the
configuration", which is necessary and, at j = 6, sufficient (then the co-type multiset equals the configuration, so the
seven cover all pairs).  Exhaustive over K_0 (all members), so complete.
Usage: py seven_config.py famfile n
"""
import sys, itertools, time
from collections import Counter
fam = [frozenset(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]; n = int(sys.argv[2])
c = len(next(iter(fam))); t0 = time.time()
subs = [s for s in range(1, 128)]
pc = lambda s: bin(s).count("1")
# Step 1 (orderly): when 2(c-1) < n-1 every co-type has size >= 3 and sum(|I|-3) = 7c - 3n =: E.  So there are
# n - (number of larger co-types) triples.  Enumerate intersecting triple multisets with label degrees <= c level by level,
# reduced up to S_7 at every level, then add the larger co-types (sizes = a partition of E into parts of size s-3).
perms = list(itertools.permutations(range(7)))
def canon(cf):
    best = None
    for p in perms:
        img = tuple(sorted(sum(1 << p[i] for i in range(7) if s >> i & 1) for s in cf))
        if best is None or img < best: best = img
    return best
E = 7 * c - 3 * n; assert 2 * (c - 1) < n - 1 and E >= 0
def partitions(m, maxp=None):
    if m == 0: yield []; return
    for p in range(min(m, maxp or m), 0, -1):
        for rest in partitions(m - p, p): yield [p] + rest
triples = [s for s in range(128) if pc(s) == 3]
def degs(cf): return [sum(s >> i & 1 for s in cf) for i in range(7)]
levels = {0: {()}}
maxT = n
for j in range(1, maxT + 1):
    nxt = set()
    for cf in levels[j - 1]:
        for t in triples:
            if any(not (t & u) for u in cf): continue
            ncf = cf + (t,)
            if max(degs(ncf)) > c: continue
            nxt.add(canon(ncf))
    levels[j] = nxt
    print(f"   triple multisets of size {j}: {len(nxt)} up to S_7 ({time.time()-t0:.0f}s)", flush=True)
configs = set()
for part in partitions(E):
    nb = len(part); m = n - nb
    if m < 0: continue
    bigsizes = [p + 3 for p in part]
    for base in levels[m]:
        def add(cf, sizes):
            if not sizes:
                if all(d == c for d in degs(cf)): configs.add(canon(cf))
                return
            sz = sizes[0]
            for s in range(128):
                if pc(s) != sz or any(not (s & u) for u in cf): continue
                ncf = cf + (s,)
                if max(degs(ncf)) > c: continue
                add(ncf, sizes[1:])
        add(base, bigsizes)
can = sorted(configs); configs = can
print(f"step 1: {len(configs)} labelled multisets, {len(can)} configurations up to S_7 ({time.time()-t0:.0f}s)", flush=True)
for cf in can: print("   sizes", sorted(Counter(pc(s) for s in cf).items()), "co-types", [bin(s)[2:].zfill(7)[::-1] for s in cf], flush=True)
# Step 2
famm = [sum(1 << x for x in K) for K in fam]
found = []
def embed(cf):
    nodes = 0
    def go(j, chosen):
        nonlocal nodes; nodes += 1
        if j == 7: return list(chosen)
        # regions: points by partial pattern over labels < j
        reg = {}
        for x in range(n):
            p = sum(1 << i for i in range(j) if chosen[i] >> x & 1); reg[p] = reg.get(p, 0) | (1 << x)
        want = Counter(s & ((1 << j) - 1) for s in cf if s >> j & 1)
        have = Counter(s & ((1 << j) - 1) for s in cf)
        if any(pc(reg.get(p, 0)) != have[p] for p in set(have) | set(reg)): return None
        for m in famm:
            if m in chosen: continue
            if all(pc(m & reg[p]) == want.get(p, 0) for p in reg):
                r = go(j + 1, chosen + [m])
                if r: return r
        return None
    r = go(0, []); return r, nodes
for cf in can:
    r, nodes = embed(cf)
    tag = "REALISED" if r else "not realised"
    print(f"step 2: config {[bin(s)[2:].zfill(7)[::-1] for s in cf][:3]}...: {tag} ({nodes} nodes, {time.time()-t0:.0f}s)", flush=True)
    if r:
        S = set(famm)
        ok = all(m in S for m in r) and all(any(m >> a & 1 and m >> b & 1 for m in r) for a in range(n) for b in range(a, n))
        print("   GOOD SEVEN:", [sorted(x for x in range(n) if m >> x & 1) for m in r], "verified:", ok, flush=True); found.append(r); break
print("VERDICT:", "good seven exists" if found else "NO good seven [exact]")
