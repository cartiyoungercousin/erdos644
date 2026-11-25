r"""Independent re-check of the FKW (m = 3) saturation certificates in logs/fkw_m3_shrunk_e*.log. [computed exact]
FKW family: V = X + Y, X = {0..11}, Y = {12..21}; edges = 12-sets A with |A & X| odd. For each WITNESS line
(co-edges K_0..K_6 as point lists, K_0 = K + {z} of size 11):
  * K_1..K_6 are co-edges of the family (10-sets, |K & X| odd)  <=>  B_i = V - K_i are edges;
  * B' = V - K_0 is an 11-set, and for z in K_0 on the class side, B = B' + {z} is an edge (so B' = B - {z});
  * B', B_1..B_6 have NO transversal of size <= 2 (brute force over all 253 point pairs incl. singletons);
  * B, B_1..B_6 DO have one (consistency with property (7,2) of the FKW family), and every such transversal P has
    P & B = {z} (Lemma 4 (ii)).
Usage: py -3.14 verify_fkw.py"""
import glob, json, re, itertools
X = set(range(12)); V = set(range(22))
def is_edge(A): return len(A) == 12 and len(A & X) % 2 == 1
def transversals(edges):
    return [P for P in itertools.combinations_with_replacement(sorted(V), 2) if all(set(P) & B for B in edges)]
for f in sorted(glob.glob('logs/fkw_m3_shrunk_e*.log'), key=lambda s: int(re.search(r'e(\d+)', s).group(1))):
    e = int(re.search(r'e(\d+)', f).group(1)); side = 'X' if e % 2 == 0 else 'Y'
    wits = [json.loads(l.split()[1]) for l in open(f) if l.startswith('WITNESS')]
    res = open(f).read().strip().splitlines()[-1]
    for W in wits:
        K = [set(k) for k in W]
        assert len(K[0]) == 11 and len(K[0] & X) == e
        Bs = [V - k for k in K[1:]]; assert all(is_edge(B) for B in Bs)
        Bp = V - K[0]
        zs = [z for z in K[0] if (z in X) == (side == 'X') and is_edge(Bp | {z})]
        assert zs, 'no incidence'
        assert transversals([Bp] + Bs) == []
        for z in zs:
            B = Bp | {z}; P = transversals([B] + Bs)
            assert P and all(set(p) & B == {z} for p in P)
    jj = 13 - e if side == 'X' else 12 - e  # |A & X| of the original edge
    print(f"class z in {side}, |A & X| = {jj}, |K' & X| = {e}: {len(wits)} certificates verified; enumerator: {res}")
