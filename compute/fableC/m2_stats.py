r"""FABLE_C section 3: size-2 co-types in the forced sevens and disjoint edge pairs in the forced profile families.
Reads compute/core12/forced_sevens.jsonl.  For every seven: co-types of size 2 (mass m_2), check of Lemma 3.1
(a co-type {i,j} forces K_i u K_j = V; the size-2 types form a star).  For every distinct logged family (profile
family on cells): does it contain two members with union V (two disjoint edges)?  <=> profiles p, p' with
p_j + p'_j >= n_j for all cells j.   [computed exact]"""
import json, re, os, itertools
from collections import Counter, defaultdict
here = os.path.dirname(os.path.abspath(__file__))
pc = lambda m: bin(m).count('1')
st = defaultdict(Counter); fams = {}
for l in open(os.path.join(here, '..', 'core12', 'forced_sevens.jsonl'), encoding='utf-8'):
    d = json.loads(l); k, n = d['k'], d['n']; T = int(re.match(r'prof_\w+?_(\d+)_(\d+)_(\d+)_', d['source']).group(2))
    Ks = d['coedges']; FULL = (1 << n) - 1; key = (k, T, n)
    typ = Counter(sum(1 << i for i in range(7) if Ks[i] >> x & 1) for x in range(n))
    two = {I: v for I, v in typ.items() if pc(I) == 2}
    for I in two:
        i, j = [a for a in range(7) if I >> a & 1]
        assert Ks[i] | Ks[j] == FULL                       # Lemma 3.1
    if len(two) >= 2:
        common = 127
        for I in two: common &= I
        assert common, 'size-2 types do not form a star'
    m2 = sum(two.values()); s = st[key]
    s['sevens'] += 1; s['m2>0'] += m2 > 0; s['max_m2'] = max(s['max_m2'], m2); s['max_leaves'] = max(s['max_leaves'], len(two))
    s['m2>0 & shape-free'] += (m2 > 0 and not d['any_shape']); s['shape-free'] += not d['any_shape']
    s['disjoint pairs among the 7 (any)'] += any(Ks[i] | Ks[j] == FULL for i, j in itertools.combinations(range(7), 2))
    if d['family_profiles'] is None: s['no family logged'] += 1; continue
    fk = (key, tuple(d['cells']), tuple(sorted(map(tuple, d['family_profiles']))))
    if fk not in fams:
        cells = d['cells']; P = d['family_profiles']
        fams[fk] = (any(all(a + b >= nj for a, b, nj in zip(p, p2, cells)) for p in P for p2 in P),
                    all(any(p[j] < cells[j] for p in P) for j in range(len(cells))))
fs = defaultdict(Counter)
for (key, cells, P), (has, nd) in fams.items():
    fs[key]['families'] += 1; fs[key]['with a disjoint edge pair'] += has; fs[key]['nondeg'] += nd; fs[key]['nondeg, no disjoint pair'] += (nd and not has)
print("instance (k,T,n): N, n-2k | sevens, with m2>0, max m2 (points), max #size-2 types | shape-free, shape-free with m2>0 | "
      "sevens containing a disjoint pair | families, families with a disjoint edge pair, nondegenerate families, nondegenerate without a disjoint edge pair")
for key in sorted(st):
    k, T, n = key; s = st[key]; f = fs[key]
    print(f"{key}: N={n/k:.3f}, n-2k={n-2*k} | {s['sevens']}, {s['m2>0']}, {s['max_m2']}, {s['max_leaves']} | {s['shape-free']}, "
          f"{s['m2>0 & shape-free']} | {s['disjoint pairs among the 7 (any)']} | {f['families']}, {f['with a disjoint edge pair']}, {f['nondeg']}, {f['nondeg, no disjoint pair']}")
