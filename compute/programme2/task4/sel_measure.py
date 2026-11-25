r"""Measure the pencil-free families produced by the SAT selectors (core9/decide_family.build, first model).
Usage: py -3.14 sel_measure.py k T n R mode [seed]   -> appends to out/measure.jsonl with group 'sel'."""
import sys, os, json
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'task1'))
sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..', 'core9')))
import decide_family as D, measure as Mz
from tau_star import Family
a = sys.argv; k, T, n, R = map(int, a[1:5]); mode = a[5]; seed = int(a[6]) if len(a) > 6 else 0
fam, sel, orders = D.build(k, T, n, R, mode, seed); full = (1 << n) - 1
F = Family(n, [full ^ K for K in fam], f'SAT pencil-free selector k={k} T={T} n={n} R={R} {mode} s{seed}')
r = Mz.measure(F, chain=(n <= 22)); r['group'] = 'sel'
import numpy as np
M = F.masks; r['zero_triples'] = int(sum(int(np.isin(M[i] ^ M[i + 1:], M).sum()) for i in range(len(M))) // 3)   # triples with x1+x2=x3
print(json.dumps(r), flush=True); open(os.path.join(HERE, 'out', 'measure.jsonl'), 'a').write(json.dumps(r) + '\n')
