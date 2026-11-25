r"""Summary of the classification of forced sevens (FABLE_C section 4).  Reads logs/classified_sevens.jsonl (records
0..600, all MILPs run) and logs/classified_sevens_from601.jsonl (records 601.., r = 3 MILPs skipped when the export
already tags a pencil or a Theorem-T triple), aligned with compute/core12/forced_sevens.jsonl.
[computed exact: witnesses re-checked by plain code in classify_sevens.py; 'no certificate' is solver-certified]"""
import json, os
from collections import Counter, defaultdict
from fractions import Fraction as F
here = os.path.dirname(os.path.abspath(__file__)); pc = lambda m: bin(m).count('1')
rd = lambda f: [json.loads(l) for l in open(os.path.join(here, 'logs', f), encoding='utf-8')]
R = rd('classified_sevens.jsonl')[:601] + rd('classified_sevens_from601.jsonl')
SRC = [json.loads(l) for l in open(os.path.join(here, '..', 'core12', 'forced_sevens.jsonl'), encoding='utf-8')]
assert all(r['source'] == d['source'] and r['n'] == d['n'] for r, d in zip(R, SRC))
print(len(R), 'of', len(SRC), 'sevens classified; undecided MILPs:', sum(r['undecided'] for r in R))
by = defaultdict(list)
for r, d in zip(R, SRC): r['coedges'] = d['coedges']; by[(r['k'], r['T'], r['n'])].append(r)
print("(k,T,n): sevens | r_min histogram | sevens with a light member (some |E_i| <= T) | "
      "shape-free: count, r_min histogram, with a light member")
tot = Counter(); totl = 0; totsf = Counter(); nsf = 0; sfl = 0
for key in sorted(by):
    L = by[key]; h = Counter(r['rmin'] for r in L); lt = sum(1 for r in L if r['light'] > 0)
    sf = [r for r in L if not r['any_shape']]
    hs = Counter(r['rmin'] for r in sf); ls = sum(1 for r in sf if r['light'] > 0)
    tot.update(h); totl += lt; totsf.update(hs); nsf += len(sf); sfl += ls
    print(f"{key}: {len(L)} | {dict(sorted(h.items()))} | {lt} | {len(sf)}, {dict(sorted(hs.items()))}, {ls}")
print('ALL:', len(R), '| r_min', dict(sorted(tot.items())), '| light', totl, '| shape-free', nsf, dict(sorted(totsf.items())), 'light', sfl)
bad = [r for r in R if (r['pencil'] or r['thmT']) and r['rmin'] > 3] + [r for r in R if r['Qp'] and r['rmin'] > 4]
print('consistency violations (shape present but r_min larger):', len(bad))
print('sevens with r_min <= 2:', sum(1 for r in R if r['rmin'] <= 2))
print('sevens with r_min = 7:', sum(1 for r in R if r['rmin'] == 7), '| light = 0:', sum(1 for r in R if r['light'] == 0),
      '| light = 0 and r_min <= 6:', sum(1 for r in R if r['light'] == 0 and r['rmin'] <= 6))
print('Q\'-only sevens (tagged Q\' but no pencil/T) with a static 3-certificate anyway:',
      sum(1 for r in R if r['Qp'] and not r['pencil'] and not r['thmT'] and r['rmin'] == 3),
      'of', sum(1 for r in R if r['Qp'] and not r['pencil'] and not r['thmT']))
# shape-free sevens with r_min = 3: how far is the witness triple from the pencil and from the Theorem-T triangle?
print("\nshape-free, r_min = 3: witness triple (first found).  d_pen = max(uncovered, n-2T-kernel, 0);"
      " d_T = max(kernel, maxpair-(T+n-2k)/2, (3n-3k-T)/2-sumpairs, 0)   [points]")
c3 = defaultdict(Counter)
for r in R:
    if r['any_shape'] or r['rmin'] != 3: continue
    n, k, T = r['n'], r['k'], r['T']; A, B, C = (r['coedges'][i] for i in r['witness'])
    kap = pc(A & B & C); g = n - pc(A | B | C); pa = [pc(A & B), pc(A & C), pc(B & C)]
    dpen = max(g, n - 2 * T - kap, 0); dT = max(F(kap), max(pa) - F(T + n - 2 * k, 2), F(3 * n - 3 * k - T, 2) - sum(pa), 0)
    c3[(k, T, n)][(str(dpen), str(dT))] += 1
for key in sorted(c3): print(' ', key, dict(sorted(c3[key].items())))
print("\nshape-free, r_min >= 4: counts by (instance, r_min, number of minimal r_min-subsets found)")
c4 = Counter((r['k'], r['T'], r['n'], r['rmin']) for r in R if not r['any_shape'] and r['rmin'] >= 4)
for key in sorted(c4): print(' ', key, c4[key])
