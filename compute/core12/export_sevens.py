r"""CORE 114 data export (for FABLE_C): every good seven forced in the profile searches at window instances, written
explicitly. Points 0..n-1, cell j = a block of consecutive points; inside a cell the points are assigned to co-types in
order. K_i = {points whose co-type contains i}. Each seven is re-checked from the bitmasks (sizes c, every pair of V
covered), and its (Sigma)-shapes among sub-triples / sub-quadruples are recomputed from the bitmasks.
Output: compute/core12/forced_sevens.jsonl, one JSON object per line:
 {k, T, n, cells, source, family_profiles, coedges: [7 ints], pencil: [...], T: [...], Qp: [...], any_shape: bool}
Usage: py -3.14 export_sevens.py"""
import glob, json, itertools, os
from fractions import Fraction as F
here = os.path.dirname(os.path.abspath(__file__))
WINDOW = {(10, 8, 21), (13, 10, 25), (13, 10, 26), (13, 10, 27), (13, 10, 28), (14, 11, 28), (14, 11, 29), (14, 11, 30),
          (15, 12, 31), (15, 12, 32), (16, 13, 34)}
pc = lambda m: bin(m).count('1')


def shapes(Ks, n, k, T):
    FULL = (1 << n) - 1; out = {'pencil': [], 'T': [], 'Qp': []}
    for tr in itertools.combinations(range(7), 3):
        A, B, C = (Ks[i] for i in tr)
        kap = pc(A & B & C)
        if (A | B | C) == FULL and kap >= n - 2 * T: out['pencil'].append(list(tr))
        if kap == 0:
            pa = [pc(A & B), pc(A & C), pc(B & C)]
            if max(pa) <= F(T + n - 2 * k, 2) and sum(pa) >= F(3 * n - 3 * k - T, 2): out['T'].append(list(tr))
    for qd in itertools.combinations(range(7), 4):
        Q = [Ks[i] for i in qd]
        deg = [sum(K >> x & 1 for K in Q) for x in range(n)]
        sig = sum(1 for d in deg if d <= 1)
        def pair_only(a, b):
            return sum(1 for x in range(n) if deg[x] == 2 and (Q[a] >> x & 1) and (Q[b] >> x & 1))
        if 2 * sig <= 3 * T - n and all(pair_only(a, b) + pair_only(c, d) + sig <= T for (a, b), (c, d) in
                                       [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]):
            out['Qp'].append(list(qd))
    return out


nout = 0
with open(os.path.join(here, 'forced_sevens.jsonl'), 'w', encoding='utf-8') as fo:
    for f in sorted(glob.glob(os.path.join(here, 'logs', 'prof_b_*.json'))):
        d = json.load(open(f, encoding='utf-8')); k, T, n, cells = d['k'], d['T'], d['n'], d['cells']
        if (k, T, n) not in WINDOW: continue
        c = n - k; FULL = (1 << n) - 1
        for e in d['sevens']:
            Ks = [0] * 7; p = 0
            for j, zj in enumerate(e['z']):
                start = sum(cells[:j]); p = start
                for I, v in sorted(((int(I), v) for I, v in zj.items())):
                    for _ in range(v):
                        for i in range(7):
                            if I >> i & 1: Ks[i] |= 1 << p
                        p += 1
                assert p == start + cells[j]
            assert all(pc(K) == c for K in Ks)
            for x, y in itertools.combinations(range(n), 2):
                assert any((K >> x & 1) and (K >> y & 1) for K in Ks), 'not a good seven'
            sh = shapes(Ks, n, k, T)
            rec = {'k': k, 'T': T, 'n': n, 'cells': cells, 'nondeg': d['nondeg'], 'source': os.path.basename(f),
                   'family_profiles': e.get('family'), 'slot_profiles': e['slots'], 'coedges': Ks,
                   'pencil': sh['pencil'], 'T': sh['T'], 'Qp': sh['Qp'], 'any_shape': bool(sh['pencil'] or sh['T'] or sh['Qp'])}
            fo.write(json.dumps(rec) + '\n'); nout += 1
print(f"wrote {nout} forced good sevens (window instances only) to forced_sevens.jsonl")
