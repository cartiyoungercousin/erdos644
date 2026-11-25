"""Robust-LP version of the level-3 truncation (CORE §77).
For a pair position (overlap o) she looks for S3 = (s_O,s_A,s_B,s_g) such that against EVERY dump some reading
has need 0 (static finish).  Sound restriction: each cell is either exhausted by S3 (s_k = m_k) or keeps >= omega
unrequested; then the dump polytope has vertices omega*e_j (j over non-exhausted cells).  Each vertex j gets a
reading R_j; one LP per assignment (s shared, one class-assignment copy per vertex).  An assignment with
different readings is accepted only after a grid check of the whole dump polytope (union of convex sets).
Usage: py -3.14 robust3.py t N [n_o]"""
import sys, itertools, numpy as np
from scipy.optimize import linprog
from fano import LINES, need
t = float(sys.argv[1]); N = float(sys.argv[2]); n_o = int(sys.argv[3]) if len(sys.argv) > 3 else 40
c = N - 1; om = N - 1 - t
KS = 'OABg'; PCT = {'O': {0,1}, 'A': {0}, 'B': {1}, 'g': set()}
READ = [{0:0,1:1}, {0:0,2:1}, {1:0,2:1}, {0:0,1:1,2:2}, {0:0,1:1,2:3}]
RNAME = ['12', '13', '23', '123line', '123tri']

def allowed(ct, lab):
    inv = {p: i for i, p in lab.items()}
    return [li for li, L in enumerate(LINES) if all((p not in inv) or (inv[p] in ct) for p in L)]

def solve(o, E, assign):
    m = {'O': o, 'A': c-o, 'B': c-o, 'g': N-2*c+o}
    verts = [j for j in KS if j not in E]
    nv = 4; cols = []  # s vars 0..3
    A_eq, b_eq, A_ub, b_ub = [], [], [], []
    bounds = [(0, m[k]) for k in KS]
    rows_eq = []; rows_ub = []
    for vi, j in enumerate(verts):
        lab = READ[assign[vi]]; keep = set(lab)
        # cells: for each pair cell k, in-part (s_k + om*[k=j]) and out-part
        cellvars = {}
        for k in KS:
            for part in ('in', 'out'):
                ct = (PCT[k] | {2}) if part == 'in' else PCT[k]
                ctk = frozenset(ct & keep)
                for li in allowed(ctk, lab):
                    cellvars.setdefault((k, part), []).append((nv, li)); nv += 1
                if (k, part) not in cellvars: cellvars[(k, part)] = []
        for k in KS:
            for part in ('in', 'out'):
                coef = {v: 1.0 for v, _ in cellvars[(k, part)]}
                si = KS.index(k); const = 0.0
                if part == 'in':
                    coef[si] = coef.get(si, 0) - 1.0; const = om if k == j else 0.0
                else:
                    coef[si] = coef.get(si, 0) + 1.0; const = m[k] - (om if k == j else 0.0)
                rows_eq.append((coef, const))
        pts = set(lab.values())
        for p in range(7):
            if p in pts: continue
            coef = {}
            for lst in cellvars.values():
                for v, li in lst:
                    if p in LINES[li]: coef[v] = 1.0
            rows_ub.append((coef, t))
    bounds += [(0, None)] * (nv - 4)
    rows_eq.append(({i: 1.0 for i in range(4)}, t))
    for k in E: rows_eq.append(({KS.index(k): 1.0}, m[k]))
    for k in verts: rows_ub.append(({KS.index(k): 1.0}, m[k] - om))
    def mat(rows):
        A = np.zeros((len(rows), nv)); b = np.zeros(len(rows))
        for r, (cf, cst) in enumerate(rows):
            for v, a in cf.items(): A[r, v] = a
            b[r] = cst
        return A, b
    Ae, be = mat(rows_eq); Au, bu = mat(rows_ub)
    res = linprog(np.zeros(nv), A_ub=Au, b_ub=bu, A_eq=Ae, b_eq=be, bounds=bounds, method='highs')
    if res.status != 0: return None
    return dict(zip(KS, res.x[:4]))

def grid_ok(o, s, n=10):
    m = {'O': o, 'A': c-o, 'B': c-o, 'g': N-2*c+o}
    cap = {k: m[k] - s[k] for k in KS}
    for comb in itertools.product(range(n+1), repeat=3):
        if sum(comb) > n: continue
        f = list(comb) + [n - sum(comb)]
        d = {k: om*f[i]/n for i, k in enumerate(KS)}
        if any(d[k] > cap[k] + 1e-9 for k in KS): continue
        cl = {}
        for k in KS:
            cl[frozenset(PCT[k] | {2})] = s[k] + d[k]; cl[frozenset(PCT[k])] = m[k] - s[k] - d[k]
        ok = False
        for lab in READ:
            keep = set(lab); cc = {}
            for ct, ms in cl.items():
                kk = frozenset(ct & keep); cc[kk] = cc.get(kk, 0) + max(ms, 0)
            v = need([(ms, kk) for kk, ms in cc.items()], lab, t + 1e-9)
            if v is not None and v <= 1e-7: ok = True; break
        if not ok: return False
    return True

def o_wins(o):
    for r in range(0, 4):
        for E in itertools.combinations(KS, r):
            verts = [j for j in KS if j not in E]
            # single reading first
            for a in range(5):
                s = solve(o, E, [a]*len(verts))
                if s: return s, E, RNAME[a]
            for assign in itertools.product(range(5), repeat=len(verts)):
                if len(set(assign)) == 1: continue
                s = solve(o, E, list(assign))
                if s and grid_ok(o, s): return s, E, '/'.join(RNAME[a] for a in assign)
    return None

if __name__ == '__main__':
    lo = max(0, 2*c - N)
    print(f"t={t} N={N} omega={om:.4f} 4eps={4*(t-.75):.4f} base={om-4*(t-.75):.4f}", flush=True)
    W = []
    for o in np.linspace(lo, c, n_o + 1):
        r = o_wins(o); W.append(r is not None)
        print(f"o={o:.4f} " + (f"WIN E={r[1]} R={r[2]} s={ {k: round(v,4) for k,v in r[0].items()} }" if r else "-"), flush=True)
