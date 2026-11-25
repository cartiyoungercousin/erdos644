"""Exact static three-anchor finish value t*(x) (units of k), as a finite min-max of linear forms.

Pencil x_a,x_b,x_c (empty triple intersection); X_i = pairwise-only part opposite i (X_a = x_b cap x_c), mass x_i;
E_i = private part of anchor i, mass 1 - x_j - x_l.  Candidate pairs: X_i--X_j (i != j), E_i--X_i.
Four free blocks L_1..L_4 (each avoided by a member, so |L_g| <= T suffices) must cover all candidate pairs.
Each point picks a nonempty pattern S of blocks; patterns on adjacent regions must intersect.  WLOG the
patterns used on a region form an antichain; on E_i the best antichain is the blocker of the one on X_i.
A config C = (A_a, A_b, A_c) of pairwise cross-intersecting antichains.  By LP duality
    v_C(x) = max_{lambda in simplex(4)} sum_R m_R(x) * min_{S in A_R} lambda(S),
and t*(x) = min_C v_C(x).  The inner function is linear on the cells of the arrangement
{lambda(P) = lambda(Q) : P, Q disjoint} u {lambda_g = 0}, so the max is attained on its finite vertex set LAM.
Everything is exact rational (fractions) for the certificates; numpy floats for scans.
This covers every seven-type in which the three anchors are three of the seven members (715 classes, all
labellings): co-type of a point = its anchor trace + its pattern.
"""
import itertools, os, pickle
from fractions import Fraction as Fr
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
MASKS = list(range(1, 16))

def is_antichain(fam):
    return all(not (a & b == a or a & b == b) for a, b in itertools.combinations(fam, 2))

def antichains():
    out = []
    for bits in range(1, 1 << 15):
        fam = [MASKS[i] for i in range(15) if bits >> i & 1]
        if is_antichain(fam): out.append(tuple(sorted(fam)))
    return out

def blocker(fam):
    """minimal transversals of fam (antichain of nonempty sets)"""
    tr = [s for s in MASKS if all(s & f for f in fam)]
    return tuple(sorted(s for s in tr if not any((u & s) == u and u != s for u in tr)))

def lam_vertices():
    hyps = []
    for g in range(4):
        v = [0] * 4; v[g] = 1; hyps.append(v)
    seen = set()
    for P in MASKS:
        for Q in MASKS:
            if P & Q or (Q, P) in seen: continue
            seen.add((P, Q))
            hyps.append([(1 if P >> g & 1 else 0) - (1 if Q >> g & 1 else 0) for g in range(4)])
    verts = set()
    for h3 in itertools.combinations(hyps, 3):
        M = [list(map(Fr, h)) + [Fr(0)] for h in h3] + [[Fr(1)] * 4 + [Fr(1)]]
        # gaussian elimination
        n = 4; A = [row[:] for row in M]; ok = True
        for c in range(n):
            p = next((r for r in range(c, n) if A[r][c] != 0), None)
            if p is None: ok = False; break
            A[c], A[p] = A[p], A[c]
            for r in range(n):
                if r != c and A[r][c] != 0:
                    f = A[r][c] / A[c][c]
                    A[r] = [a - f * b for a, b in zip(A[r], A[c])]
        if not ok: continue
        lam = tuple(A[i][4] / A[i][i] for i in range(n))
        if min(lam) >= 0: verts.add(lam)
    return sorted(verts)

def lam_S(lam, S):
    return sum(lam[g] for g in range(4) if S >> g & 1)

def build(cache=True):
    fn = os.path.join(HERE, 'logs', 'tstar_tables.pkl')
    if cache and os.path.exists(fn): return pickle.load(open(fn, 'rb'))
    AC = antichains()
    idx = {a: i for i, a in enumerate(AC)}
    n = len(AC)
    cross = np.zeros((n, n), bool)
    for i, a in enumerate(AC):
        for j, b in enumerate(AC):
            cross[i, j] = all(s & t for s in a for t in b)
    LAM = lam_vertices()
    # coefficient of antichain at lambda: min over S of lambda(S)
    coefF = [[min(lam_S(l, S) for S in a) for l in LAM] for a in AC]
    coef = np.array([[float(c) for c in row] for row in coefF])          # n x L
    blk = [idx[blocker(a)] for a in AC]
    perms = list(itertools.permutations(range(4)))
    def pm(S, p): return sum(1 << p[g] for g in range(4) if S >> g & 1)
    pidx = [[idx[tuple(sorted(pm(S, p) for S in a))] for a in AC] for p in perms]   # antichain image index
    seen, configs = set(), []
    for i in range(n):
        for j in range(n):
            if not cross[i, j]: continue
            for l in range(n):
                if cross[i, l] and cross[j, l]:
                    key = min((P[i], P[j], P[l]) for P in pidx)        # S4 on blocks: same value function
                    if key not in seen: seen.add(key); configs.append(key)
    configs = np.array(configs)
    # coefficient tensor K[c, lam, region]
    K = np.stack([coef[configs[:, 0]], coef[configs[:, 1]], coef[configs[:, 2]],
                  coef[np.array(blk)[configs[:, 0]]], coef[np.array(blk)[configs[:, 1]]],
                  coef[np.array(blk)[configs[:, 2]]]], axis=2)
    # prune dominated configs (K_c' <= K_c entrywise => c dominated), greedy on sorted sums
    order = np.argsort(K.sum(axis=(1, 2)))
    keep = []
    for c in order:
        if any(np.all(K[d] <= K[c] + 1e-12) for d in keep[-4000:]): continue
        keep.append(c)
    configs, K = configs[keep], K[keep]
    T = dict(AC=AC, LAM=LAM, coefF=coefF, blk=blk, configs=configs, K=K)
    if cache: pickle.dump(T, open(fn, 'wb'))
    return T

TAB = None
def tab():
    global TAB
    if TAB is None: TAB = build()
    return TAB

def masses(x):
    xa, xb, xc = x
    return [xa, xb, xc, 1 - xb - xc, 1 - xa - xc, 1 - xa - xb]

def tstar(x, ret=False):
    T = tab(); m = np.array([float(v) for v in masses(x)])
    vals = (T['K'] @ m).max(axis=1)          # v_C(x) for each config
    c = int(np.argmin(vals))
    return (vals[c], c) if ret else vals[c]

def tstar_many(X):
    """X: array (N,3) -> t* for each row"""
    T = tab()
    X = np.asarray(X, float)
    M = np.stack([X[:, 0], X[:, 1], X[:, 2], 1 - X[:, 1] - X[:, 2], 1 - X[:, 0] - X[:, 2], 1 - X[:, 0] - X[:, 1]], 1)
    out = np.empty(len(X))
    for s in range(0, len(X), 256):
        V = np.einsum('clr,nr->ncl', T['K'], M[s:s + 256])
        out[s:s + 256] = V.max(axis=2).min(axis=1)
    return out

def tstar_exact(x):
    """exact rational t*(x) for rational x: min over ALL configs (unpruned) of max over LAM"""
    T = tab(); m = [Fr(v) for v in masses(x)]
    AC, coefF, blk, LAM = T['AC'], T['coefF'], T['blk'], T['LAM']
    best = None
    for (i, j, l) in T['configs']:
        regs = [i, j, l, blk[i], blk[j], blk[l]]
        v = max(sum(m[r] * coefF[regs[r]][q] for r in range(6)) for q in range(len(LAM)))
        if best is None or v < best[0]: best = (v, (i, j, l))
    return best

def describe(c_id):
    T = tab(); i, j, l = T['configs'][c_id] if not isinstance(c_id, tuple) else c_id
    AC, blk = T['AC'], T['blk']
    f = lambda a: '{' + ','.join(''.join(str(g + 1) for g in range(4) if s >> g & 1) for s in AC[a]) + '}'
    return 'Xa%s Xb%s Xc%s | Ea%s Eb%s Ec%s' % (f(i), f(j), f(l), f(blk[i]), f(blk[j]), f(blk[l]))

if __name__ == '__main__':
    T = build(cache=False)
    print('antichains', len(T['AC']), 'lambda vertices', len(T['LAM']), 'configs kept', len(T['configs']))
