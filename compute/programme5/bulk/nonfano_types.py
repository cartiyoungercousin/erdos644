"""Classify the non-Fano-only good sevens found by programme4/cells/fano_suff.py (two-cell profile families).
For each witness: co-type support (subsets of [7], bitmask), masses per cell, and the S7-class of the
maximal intersecting families containing the support (smallest LP value among them, from the 716-class table).
usage: py -3.14 nonfano_types.py   (reads ../../programme4/cells/certs/fano_*.jsonl)"""
import json, glob, os, itertools, collections
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__))
CERTS = os.path.join(HERE, '..', '..', 'programme4', 'cells', 'certs')
rows = json.load(open(os.path.join(HERE, '..', '..', 'programme2', 'verify', 'out', 'maxint7_classes_lp.json')))
classes = []
for i, r in enumerate(rows):
    v = int(r['mask'], 16)
    classes.append((i, v, None if r['lp'] == 'None' else Fr(r['lp']), r['fano']))
PERMS = list(itertools.permutations(range(7)))
def permset(S, p):
    return sum(1 << p[i] for i in range(7) if S >> i & 1)
def classes_containing(supp):
    """all (class idx) whose some relabelling contains supp (as a subset of the 128 sets)."""
    out = set()
    for p in PERMS:
        bits = 0
        for S in supp: bits |= 1 << permset(S, p)
        for (i, v, lp, fano) in classes:
            if i in out: continue
            if v & bits == bits: out.add(i)
    return out
def popc(x): return bin(x).count('1')
wit = []
for f in sorted(glob.glob(os.path.join(CERTS, 'fano_k*_T*_q2.jsonl'))):
    for line in open(f):
        r = json.loads(line)
        for w in r['nonfano_only']:
            if w.get('fano_status') != 'FOUND': continue
            mass = collections.Counter()
            for cell, d in w['x'].items():
                for S, c in d.items(): mass[int(S)] += c
            wit.append(dict(k=r['k'], a=r['a'], n=r['n'], tau=w['tau'], J=w['J'], mass=dict(mass)))
print('witnesses', len(wit))
cache = {}
summary = collections.Counter()
for w in wit:
    supp = tuple(sorted(w['mass']))
    # minimise support to the inclusion-minimal sets (up-closure is what matters)
    mins = tuple(S for S in supp if not any(T != S and T & S == T for T in supp))
    key = mins
    if key not in cache:
        cc = classes_containing(mins)
        best = min((classes[i][2] for i in cc if classes[i][2] is not None), default=None)
        cache[key] = (len(cc), best)
    ncls, best = cache[key]
    sizes = collections.Counter(popc(S) for S in w['mass'] for _ in range(w['mass'][S]))
    deg = {7 - s: c for s, c in sorted(sizes.items())}   # degree = number of the 7 members containing the point
    w['deg'] = deg; w['bestLP'] = str(best); w['ncls'] = ncls
    summary[(str(best), tuple(sorted(deg.items())))] += 1
    print(w['k'], w['a'], 'n/k=%.3f' % (w['n'] / w['k']), 'tau', w['tau'], 'deg', deg, 'min-LP class', best,
          'n_classes', ncls, 'cotypes', sorted((bin(S)[2:].zfill(7)[::-1], c) for S, c in w['mass'].items()))
print('summary (best LP of a containing class, degree profile): count')
for kk, v in summary.most_common(): print(kk, v)
