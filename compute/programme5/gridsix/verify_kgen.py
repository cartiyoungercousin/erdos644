"""Independent checker for a kgen INFEASIBLE certificate.  No code shared with kgen.py / cover.py.
Input: logs/kgen_<tag>.out (header: R0 type, families, box, t, krange) and logs/kgen_<tag>.plans.jsonl.
 (1) every plan: on its support (possible atoms minus required-empty ones), every alive atom pair of its frame has
     intersecting used vectors, each such atom is fully placed, and no support atom lies in every frame member;
 (2) fresh SCIP model of the adversary (triple in the box, K avoiding R0, S*-traces, krange option, one M1 per
     family escaping all its plans or the family inapplicable; K escaping all K-level plans), escape margin 1e-6 (a request of size exactly t is allowed, so ties are closures):
     must be INFEASIBLE;
 (3) random sampling of (triple, K, M1) as a sanity check of (2).
usage: py verify_kgen.py tag [nsamples]"""
import sys, json, itertools, re, ast
import numpy as np
from ortools.linear_solver import pywraplp

BANDS = [(0.0, 45 / 12), (5.0, 73 / 12), (80 / 12, 14.0)]
BASE = ['EF', 'EG', 'FG', 'E', 'F', 'G']
CELLS = BASE + [b + 'K' for b in BASE] + ['K']
R0 = {'A': lambda q, y, z, t: {'EF': q, 'EG': y, 'FG': z, 'F': t - q - y - z},
      'A_G': lambda q, y, z, t: {'EF': q, 'EG': y, 'FG': z, 'G': t - q - y - z},
      'noZ': lambda q, y, z, t: {'EF': q, 'EG': y, 'F': t - q - y},
      'partY': lambda q, y, z, t: {'EF': q, 'FG': z, 'EG': t - q - z},
      'partYnoZ': lambda q, y, z, t: {'EF': q, 'EG': t - q},
      'partX': lambda q, y, z, t: {'EG': y, 'FG': z, 'EF': t - y - z}}
FAMS = {'XAH': (['GK', 'EK', 'K'], 'EF'), 'YBH': (['FK', 'EK', 'K'], 'EG'), 'XA': (['GK'], 'EF'), 'YB': (['FK'], 'EG'),
        'XAY': (['GK', 'EGK', 'EK', 'K'], 'EF'), 'YBX': (['FK', 'EFK', 'EK', 'K'], 'EG'),
        'XAZ': (['GK', 'FGK', 'EK', 'K'], 'EF'), 'YBZ': (['FK', 'FGK', 'EK', 'K'], 'EG')}


def bsize(b, q, y, z):
    return {'EF': q, 'EG': y, 'FG': z, 'E': 14 - q - y, 'F': 14 - q - z, 'G': 14 - y - z}[b]


def member(a, m):
    c, bit = a
    return bit == 1 if m == 'M' else m in c


def dec(x):
    c, b = x.rsplit('|', 1); return (c, int(b))


def main(tag, nsamp=3000):
    hdr = open('logs/kgen_%s.out' % tag).readline()
    r0type = hdr.split()[1]
    fams = ast.literal_eval(re.search(r'families (\[[^\]]*\])', hdr).group(1))
    box = tuple(float(v) for v in re.search(r'z lo,hi\) \(([^)]*)\)', hdr).group(1).split(','))
    t = float(re.search(r' t ([0-9.]+)', hdr).group(1)); kr = re.search(r'krange (\w+)', hdr).group(1)
    print(tag, 'R0', r0type, 'fams', fams, 'box', box, 't', t, 'krange', kr)
    kpl, mpl = [], {f: [] for f in fams}; bad = 0
    for line in open('logs/kgen_%s.plans.jsonl' % tag):
        d = json.loads(line); vec = {dec(a): v for a, v in d['vec'].items()}; need = set(dec(a) for a in d['need'])
        fr, r = d['frame'], d['r']
        if d['lvl'] == 'K': poss = [(c, 0) for c in CELLS]
        else:
            full, fill = FAMS[d['lvl']]; poss = [(c, 1) for c in CELLS if c not in full] + [(c, 0) for c in CELLS] + [('', 1)]
        sup = [a for a in poss if a not in need]
        for a in sup:
            if all(member(a, m) for m in fr): bad += 1                     # dead atom left in the support
        al = [(p, q) for p, q in itertools.combinations_with_replacement(sup, 2) if all(member(p, m) or member(q, m) for m in fr)]
        for a in set(x for pq in al for x in pq):
            if a not in vec or abs(sum(f for _, f in vec[a]) - 1) > 1e-6: bad += 1
        for p, q in al:
            for v, fv in vec.get(p, []):
                for w, gw in vec.get(q, []):
                    if fv > 1e-12 and gw > 1e-12 and not any(x and u for x, u in zip(v, w)): bad += 1
        coef = {a: [sum(f for v, f in lst if v[i]) for i in range(r)] for a, lst in vec.items()}
        (kpl if d['lvl'] == 'K' else mpl[d['lvl']]).append((coef, sorted(need), r))
    print('  plans: K %d, M1 %s; coverage/dead violations %d' % (len(kpl), {f: len(p) for f, p in mpl.items()}, bad))

    sv = pywraplp.Solver.CreateSolver('SCIP')
    q = sv.NumVar(box[0], box[1], ''); y = sv.NumVar(box[2], box[3], ''); z = sv.NumVar(box[4], box[5], '')
    r0 = R0[r0type](q, y, z, t)
    k = {b: sv.NumVar(0, 14, '') for b in BASE}; ko = sv.NumVar(0, 14, '')
    S = {}
    for b in BASE:
        bs = bsize(b, q, y, z); sv.Add(bs >= 0); sv.Add(k[b] + r0.get(b, 0) <= bs)
        if b in r0: sv.Add(r0[b] >= 0)
        S[b + 'K'] = k[b]; S[b] = bs - k[b]
    S['K'] = ko; sv.Add(sum(k.values()) + ko == 14)
    def band(e):
        ys = [sv.BoolVar('') for _ in BANDS]; sv.Add(sum(ys) == 1)
        sv.Add(e >= sum(lo * w for (lo, hi), w in zip(BANDS, ys))); sv.Add(e <= sum(hi * w for (lo, hi), w in zip(BANDS, ys)))
    for P in 'EFG': band(sum(k[b] for b in BASE if P in b))
    if kr == 'hand': sv.Add(k['F'] >= t - y); sv.Add(k['G'] >= t - q)
    elif kr == 'comp':
        w = sv.BoolVar(''); sv.Add(k['F'] <= t - y + 80 * w); sv.Add(k['G'] <= t - q + 80 * (1 - w))
    def escape(plans, size, extra=None):
        for coef, need, r in plans:
            ys = [] if extra is None else [extra()]
            for a in need:
                u = sv.BoolVar(''); ys.append(u); sv.Add(size(a) >= 1e-7 * u)
            for i in range(r):
                u = sv.BoolVar(''); ys.append(u); sv.Add(sum(coef[a][i] * size(a) for a in coef) >= t + 1e-6 - 80 * (1 - u))
            sv.Add(sum(ys) >= 1)
    escape(kpl, lambda a: S[a[0]])
    for f in fams:
        full, fill = FAMS[f]
        app = sv.BoolVar(''); cap = sv.BoolVar('')
        fa = t - sum(S[c] for c in full)
        sv.Add(fa >= -80 * (1 - app)); sv.Add(fa <= -1e-7 + 80 * app)
        sv.Add(fa <= S[fill] + 80 * cap); sv.Add(fa >= S[fill] - 80 * (1 - cap))
        m = {c: sv.NumVar(0, 14, '') for c in CELLS}; oo = sv.NumVar(0, 14, ''); sv.Add(sum(m.values()) + oo == 14)
        for c in CELLS:
            sv.Add(m[c] <= S[c])
            if c in full: sv.Add(m[c] <= 80 * (1 - app))
            elif c == fill: sv.Add(m[c] <= S[c] - fa + 80 * cap + 80 * (1 - app)); sv.Add(m[c] <= 80 * (1 - cap) + 80 * (1 - app))
        for P in 'EFGK': band(sum(m[c] for c in CELLS if P in c))
        def size(a, m=m, oo=oo):
            return oo if a[0] == '' else (m[a[0]] if a[1] == 1 else S[a[0]] - m[a[0]])
        def na(app=app):
            u = sv.BoolVar(''); sv.Add(u <= 1 - app); return u
        escape(mpl[f], size, na)
    sv.SetTimeLimit(175000)
    st = sv.Solve()
    res = {pywraplp.Solver.INFEASIBLE: 'INFEASIBLE', pywraplp.Solver.OPTIMAL: 'FEASIBLE', pywraplp.Solver.FEASIBLE: 'FEASIBLE'}.get(st, 'NOT SOLVED %d' % st)
    print('  independent SCIP re-solve (margin 1e-6):', res, ('triple %s' % [round(v.solution_value(), 6) for v in (q, y, z)]) if res == 'FEASIBLE' else '')
    if res == 'FEASIBLE':
        print('  K =', json.dumps({b: k[b].solution_value() for b in BASE} | {'out': ko.solution_value()}))
        print('  triple =', json.dumps([v.solution_value() for v in (q, y, z)]))
    print('  VERDICT', 'OK' if bad == 0 and res == 'INFEASIBLE' else 'CHECK')


if __name__ == '__main__':
    main(sys.argv[1], *(int(x) for x in sys.argv[2:]))
