r"""FABLE_A T3 [computed exact per instance]: the robust mixed design on real sets.
Two-class reversed rule on V = range(n): reply to S is S + (om lowest of V\S) if sigma(S) = 'a', S + (om highest) if 'b'.
Selector tested: threshold  sigma(S) = 'a' iff |S & Y_a| >= j0  (b-dominant below the switch j* = j0, a at j0).
Design (integer MILP, same rows as t2d): f-lines = the three lines through class 0, quadrangle coloured by `quad`;
a-requests: |S&Y_a| = j0, |S&I| = i - j0, S&Y_b empty; b-requests: |S&Y_a| = jb < j0, S&Y_b empty; f-requests: the line, padded.
The rule is applied verbatim and all pairs are checked.  Usage: py t3_finite_check.py"""
import itertools, sys
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]

def reply(S, n, om, col):
    out = [x for x in range(n) if x not in S]
    D = out[:om] if col == 'a' else out[-om:]
    return set(S) | set(D)

def design(k, T, n, j0, quad, i):
    om = n - k - T; m = n - 2*om
    reg = [om, om, i, m - i]; nv = 28 + 4; idx = lambda c, r: 4*c + r
    A = []; ub = []
    def row(L, regs):
        v = np.zeros(nv)
        for c in L:
            for r in regs: v[idx(c, r)] = 1
        return v
    for n_, (L, ty) in enumerate(zip(LINES, "fff" + quad)):
        if ty == 'a':
            A.append(row(L, [1])); ub.append(0); A.append(row(L, [3])); ub.append(T - i)
        elif ty == 'b':
            jb = 28 + n_ - 3
            v = row(L, [0]); v[jb] = -1; A.append(v); ub.append(0)          # Y_a part <= jb
            v = row(L, [2, 3]); v[jb] = 1; A.append(v); ub.append(T)        # M part <= T - jb (finite k: any profile on I)
        else:
            A.append(row(L, [0,1,2,3])); ub.append(T)
    Aeq = np.zeros((4, nv))
    for r in range(4):
        for c in range(7): Aeq[r, idx(c, r)] = 1
    cons = [LinearConstraint(np.array(A), -np.inf, np.array(ub)), LinearConstraint(Aeq, np.array(reg), np.array(reg))]
    res = milp(np.zeros(nv), constraints=cons, integrality=np.ones(nv),
               bounds=Bounds(np.zeros(nv), np.array([n]*28 + [max(j0 - 1, 0)]*4)))
    if res.status != 0: return None
    x = np.round(res.x).astype(int); return x[:28].reshape(7, 4), x[28:]

def run(k, T, n, j0, quad):
    om = n - k - T; m = n - 2*om
    i = round(j0*m/(m - T + j0)) if j0 > 0 else 0
    d = design(k, T, n, j0, quad, i)
    if d is None: return "no integer design"
    w, jbs = d
    YA = list(range(om)); M = list(range(om, n - om)); YB = list(range(n - om, n)); I = M[:i]; R = M[i:]
    pools = [YA[:], YB[:], I[:], R[:]]; cls = [[[], [], [], []] for _ in range(7)]
    for r in range(4):
        p = pools[r][:]
        for c in range(7):
            cls[c][r] = p[:w[c][r]]; p = p[w[c][r]:]
    sigma = lambda S: 'a' if len(set(S) & set(YA)) >= j0 else 'b'
    members = []
    for n_, (L, ty) in enumerate(zip(LINES, "fff" + quad)):
        Lr = [sum((cls[c][r] for c in L), []) for r in range(4)]
        if ty == 'a':
            W = Lr[3] + [x for x in R if x not in Lr[3]][:T - i - len(Lr[3])]
            S = set(YA[:j0]) | set(I[j0:]) | set(W)          # leaves exactly j0 of I and om - j0 of Y_a unrequested
        elif ty == 'b':
            jb = jbs[n_ - 3]
            ya = Lr[0] + [x for x in YA if x not in Lr[0]][:jb - len(Lr[0])]
            mm = Lr[2] + Lr[3]; mm = mm + [x for x in M if x not in mm][:T - len(ya) - len(mm)]
            S = set(ya) | set(mm)
        else:
            base = sum(Lr, []); S = set(base) | set([x for x in range(n) if x not in base][:T - len(base)])
        assert len(S) == T, (ty, len(S))
        col = sigma(S)
        if ty in 'ab' and col != ty: return f"colour mismatch on a {ty}-line"
        members.append(reply(S, n, om, col))
    bad = [(x, y) for x in range(n) for y in range(x, n) if not any(x in K and y in K for K in members)]
    return "GOOD SEVEN" if not bad else f"{len(bad)} uncovered pairs"

if __name__ == "__main__":
    for (k, T, n) in [(40, 31, 76), (40, 31, 78), (40, 31, 80), (40, 31, 82), (40, 31, 84), (60, 46, 115), (60, 46, 124)]:
        om = n - k - T
        for j0 in range(1, om // 3 + 1):
            res = {}
            for quad in ["aabb", "abab", "abba", "baab", "baba", "bbaa"]:
                res[quad] = run(k, T, n, j0, quad)
                if res[quad] == "GOOD SEVEN": break
            print(f"(k,T,n)=({k},{T},{n}) om={om} switch j0={j0}: {quad}: {res[quad]}", flush=True)
