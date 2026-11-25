r"""CORE 55.5, decisive method (v2).  Step 1 [family-free, computed exact]: all co-type configurations of a pair-cover of
n = 15 points by seven 7-sets (more generally 2(c-1) < n-1, E = 7c - 3n): multisets of n subsets of [7], pairwise
intersecting, each label in exactly c of them, every subset of size >= 3 (so sum(|I|-3) = E).
Generation: (a) distinct intersecting triple families (supports) up to S_7, orderly; (b) multiplicities mu_T >= 1 with
sum mu = number of triples, label degrees <= c; (c) the larger co-types (sizes from the partitions of E), meeting
everything; keep degree exactly c; reduce up to S_7.
Step 2 [computed exact]: realise each configuration in the family by members chosen label by label with exact Venn counts
(as in seven_config.py).  Usage: py seven_config2.py famfile n
"""
import sys, itertools, time
from collections import Counter
fam = [frozenset(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]; n = int(sys.argv[2])
c = len(next(iter(fam))); t0 = time.time(); pc = lambda s: bin(s).count("1")
E = 7 * c - 3 * n; assert 2 * (c - 1) < n - 1 and E >= 0
perms = list(itertools.permutations(range(7)))
def img(cf, p): return tuple(sorted(sum(1 << p[i] for i in range(7) if s >> i & 1) for s in cf))
def canon(cf): return min(img(cf, p) for p in perms)
triples = [s for s in range(128) if pc(s) == 3]
# (a) supports
lev = [{()}]; supports = {()}
while lev[-1]:
    nxt = set()
    for S in lev[-1]:
        for t in triples:
            if t in S or any(not (t & u) for u in S): continue
            nxt.add(canon(S + (t,)))
    lev.append(nxt); supports |= nxt
print(f"(a) intersecting triple supports up to S_7: {len(supports)} (sizes {[len(l) for l in lev]}) ({time.time()-t0:.0f}s)", flush=True)
def partitions(m, maxp=None):
    if m == 0: yield []; return
    for p in range(min(m, maxp or m), 0, -1):
        for rest in partitions(m - p, p): yield [p] + rest
configs = set()
for part in partitions(E):
    nb = len(part); m = n - nb; bigsizes = [p + 3 for p in part]
    for S in supports:
        if not S or len(S) > m: continue
        S = list(S)
        # (b) multiplicities
        def mult(i, left, deg, cur):
            if i == len(S):
                if left == 0: yield list(cur)
                return
            t = S[i]; lab = [j for j in range(7) if t >> j & 1]
            for mu in range(1, left - (len(S) - i - 1) + 1):
                nd = deg[:]
                for j in lab: nd[j] += mu
                if max(nd) > c: break
                cur.append(mu); yield from mult(i + 1, left - mu, nd, cur); cur.pop()
        for mus in mult(0, m, [0] * 7, []):
            base = tuple(t for t, mu in zip(S, mus) for _ in range(mu))
            deg = [sum(s >> j & 1 for s in base) for j in range(7)]
            if any(d + nb < c for d in deg): continue
            # (c) larger co-types
            def add(cf, sizes, dg):
                if not sizes:
                    if all(d == c for d in dg): configs.add(canon(cf))
                    return
                sz = sizes[0]
                for s in range(128):
                    if pc(s) != sz or any(not (s & u) for u in cf): continue
                    nd = [dg[j] + (s >> j & 1) for j in range(7)]
                    if max(nd) > c or any(d + len(sizes) - 1 < c for d in nd): continue
                    add(cf + (s,), sizes[1:], nd)
            add(base, bigsizes, deg)
can = sorted(configs)
print(f"(b,c) configurations up to S_7: {len(can)} ({time.time()-t0:.0f}s)", flush=True)
for cf in can: print("   r-profile", sorted(Counter(pc(s) for s in cf).items()), "co-types", " ".join(bin(s)[2:].zfill(7)[::-1] for s in cf), flush=True)
famm = [sum(1 << x for x in K) for K in fam]; famset = set(famm)
def embed(cf):
    nodes = 0
    def go(j, chosen):
        nonlocal nodes; nodes += 1
        if j == 7: return list(chosen)
        reg = {}
        for x in range(n):
            p = sum(1 << i for i in range(j) if chosen[i] >> x & 1); reg[p] = reg.get(p, 0) | (1 << x)
        have = Counter(s & ((1 << j) - 1) for s in cf)
        if any(pc(reg.get(p, 0)) != have[p] for p in set(have) | set(reg)): return None
        want = Counter(s & ((1 << j) - 1) for s in cf if s >> j & 1)
        for m in famm:
            if all(pc(m & reg[p]) == want.get(p, 0) for p in reg):
                r = go(j + 1, chosen + [m])
                if r: return r
        return None
    return go(0, []), nodes
found = None
for k_, cf in enumerate(can):
    r, nodes = embed(cf)
    print(f"step 2: config {k_}: {'REALISED' if r else 'not realised'} ({nodes} nodes, {time.time()-t0:.0f}s)", flush=True)
    if r:
        ok = all(m in famset for m in r) and all(any(m >> a & 1 and m >> b & 1 for m in r) for a in range(n) for b in range(a, n))
        print("   GOOD SEVEN:", [sorted(x for x in range(n) if m >> x & 1) for m in r], "verified:", ok, flush=True); found = r; break
print("VERDICT:", "good seven exists" if found else "NO good seven [exact]")
