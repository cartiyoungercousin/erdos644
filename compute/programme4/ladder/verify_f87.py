r"""Independent plain-Python check of the f(8,7) >= 7 witness (no solver, no shared code with the searches).
Input: co-edge file (7-subsets K of V = {0..14}); the family is H = {V \ K}, 8-uniform.
Checks:
 (1) the co-edges are distinct 7-subsets of V;
 (2) tau(H) >= 7: every 6-set X of V lies in some co-edge (then the 9-set V \ X contains a member, so X is no
     transversal);  tau(H) <= 7: any 7-set that is not a co-edge meets every member;
 (3) the configuration list is well formed: each line is a multiset of 15 co-types (subsets of {0..6}) of size >= 3,
     pairwise intersecting, each label in exactly 7 of them; lines pairwise non-isomorphic under S_7.
 (4) the embedding logs report every class (0..67) as NONE / INFEASIBLE.
Seven-freeness itself rests on (3) + (4) + completeness of the class list (two enumerators, cotypes2.js and cotypes.js).
Usage: py verify_f87.py coedges configfile embedlog cpsatlog
"""
import sys, itertools

V = range(15)
K = [tuple(sorted(map(int, l.split()))) for l in open(sys.argv[1]) if l.strip()]
assert all(len(k) == 7 and len(set(k)) == 7 and all(0 <= x < 15 for x in k) for k in K)
Ks = set(map(frozenset, K)); assert len(Ks) == len(K)
print(f"(1) {len(K)} distinct co-edges (7-subsets of [15]); members = complements, 8-uniform")
bad = 0
for X in itertools.combinations(V, 6):
    Xs = frozenset(X)
    if not any(Xs | {y} in Ks for y in V if y not in Xs): bad += 1
print(f"(2) 6-sets not inside any co-edge: {bad}  -> tau >= 7: {bad == 0}")
S = next(frozenset(s) for s in itertools.combinations(V, 7) if frozenset(s) not in Ks)
members = [frozenset(V) - k for k in Ks]
assert all(S & B for B in members)
print(f"    the 7-set {sorted(S)} meets every member -> tau <= 7; so tau = 7")
cfgs = []
for line in open(sys.argv[2]):
    if not line.strip(): continue
    ms = []
    for t in line.split("|")[0].split():
        a, b = map(int, t.split(":")); ms += [a] * b
    assert len(ms) == 15 and all(bin(s).count("1") >= 3 and s < 128 for s in ms)
    assert all(a & b for a in ms for b in ms)
    assert all(sum(1 for s in ms if s >> i & 1) == 7 for i in range(7))
    cfgs.append(tuple(sorted(ms)))
canon = set()
for cf in cfgs:
    canon.add(min(tuple(sorted(sum(1 << p[i] for i in range(7) if s >> i & 1) for s in cf)) for p in itertools.permutations(range(7))))
print(f"(3) {len(cfgs)} configurations, all valid pair-covering co-type multisets, pairwise non-isomorphic: {len(canon) == len(cfgs)}")
emb = [l for l in open(sys.argv[3]) if l.startswith("class")]
cps = [l for l in open(sys.argv[4]) if l.startswith("class")]
ok_e = len(emb) == len(cfgs) and all("NONE" in l for l in emb)
ok_c = len(cps) == len(cfgs) and all("INFEASIBLE" in l for l in cps)
print(f"(4) embed.js: {sum('NONE' in l for l in emb)}/{len(cfgs)} NONE; CP-SAT: {sum('INFEASIBLE' in l for l in cps)}/{len(cfgs)} INFEASIBLE -> {ok_e and ok_c}")
