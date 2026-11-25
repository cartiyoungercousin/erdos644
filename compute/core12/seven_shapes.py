r"""CORE 114: structure of the good sevens forced in the profile searches.  For every logged good seven: the total co-type
multiset (sum over cells), its size profile, whether its 3-element co-types lie in a Fano plane, the (Sigma)-shapes among
its sub-triples / sub-quadruples (from profile_search.py), and, for sevens without one, the Theorem-T / Q' / pencil
margins (how far the best sub-configuration is from each shape).  [computed exact on the logged data]
Usage: py -3.14 seven_shapes.py "logs/prof_b_*.json" """
import sys, glob, json, itertools
from collections import Counter
from fractions import Fraction as F

FANO_LINES = None
def is_fano(trs):
    # three-sets pairwise meeting in exactly one point, 7 of them, = a Fano plane; subsets of one: check by extension
    trs = set(trs)
    if any(bin(a & b).count('1') != 1 for a, b in itertools.combinations(trs, 2)): return False
    return True  # pairwise meeting in one point <=> contained in a Fano plane (for 3-sets on 7 points, linear space)

def margins(tot, n, k, T):
    best = {'pencil': None, 'T': None, "Q'": None}
    for tr in itertools.combinations(range(7), 3):
        reg = Counter()
        for I, v in tot.items(): reg[sum(1 << a for a, i in enumerate(tr) if I >> i & 1)] += v
        kap = reg[7]
        m = max(reg[0], (n - 2 * T) - kap, 0)  # pencil deficit: uncovered points, missing kernel
        best['pencil'] = m if best['pencil'] is None else min(best['pencil'], m)
        pa = [reg[3] + kap, reg[5] + kap, reg[6] + kap]
        mt = max(kap, max(pa) - F(T + n - 2 * k, 2), F(3 * n - 3 * k - T, 2) - sum(pa), 0)
        best['T'] = mt if best['T'] is None else min(best['T'], mt)
    for qd in itertools.combinations(range(7), 4):
        reg = Counter()
        for I, v in tot.items(): reg[sum(1 << a for a, i in enumerate(qd) if I >> i & 1)] += v
        sig = sum(reg[r] for r in range(16) if bin(r).count('1') <= 1)
        mq = max(sig - F(3 * T - n, 2), max(reg[a] + reg[b] + sig - T for a, b in [(3, 12), (5, 10), (9, 6)]), 0)
        best["Q'"] = mq if best["Q'"] is None else min(best["Q'"], mq)
    return best

files = [f for a in sys.argv[1:] for f in glob.glob(a)]
tot_sev = 0; no = 0; kinds = Counter(); desc = Counter(); marg = Counter()
for f in files:
    d = json.load(open(f, encoding='utf-8')); n, k, T = d['n'], d['k'], d['T']
    for e in d['sevens']:
        tot_sev += 1; tot = Counter()
        for zj in e['z']:
            for I, v in zj.items(): tot[int(I)] += v
        for a, _ in e['shapes']: kinds[a] += 1
        if e['shapes']: continue
        no += 1
        sizes = tuple(sorted(Counter(bin(I).count('1') for I in tot.elements()).items()))
        trs = [I for I in tot if bin(I).count('1') == 3]
        desc[(f"k={k},T={T},n={n}", sizes, 'Fano-type triples' if is_fano(trs) else 'non-Fano triples')] += 1
        m = margins(tot, n, k, T); marg[(f"k={k},T={T},n={n}", tuple((a, str(b)) for a, b in m.items()))] += 1
print(f"{tot_sev} logged good sevens; sub-shapes found: {dict(kinds)}; sevens with no (Sigma)-shape among their members: {no}")
print("co-type size profiles of shape-free sevens (count):")
for key, v in sorted(desc.items()): print("  ", v, key)
print("smallest shape deficits in shape-free sevens (pencil: points; T, Q': mass in points):")
for key, v in sorted(marg.items()): print("  ", v, key)
