r"""CORE 105: first-order exponents (nats per k) for covering designs C(n, c, T), c = n - k.  [computed float]
Phi    = N h(t/N) - c h(t/c)   : log of the Schoenheim/counting minimum |C| (= log size of the threshold random design)
Pool   = (N-w) h(t/(N-w))      : log size of the pool family {K : K >= Y}, |Y| = w (inclusion-minimal, T-covering)
gamma  = (N-t) h(w/(N-t))      : -log density of the threshold random design
For a shape on r members with certifying polytope P (Venn masses), Hmax = max_{v in P} N H(v/N) and
  per-member log-count  D_shape = Hmax - r*gamma - Phi     (> 0: supercritical, every member in e^{D k} shapes on average)
Shapes: Q' (CORE 95(a)), pencil (b) (union V, triple >= N-2t), Theorem-T triangle (c) (triple = 0), Fano good seven
(symmetric max-entropy on the Fano upset; a lower bound for 'any good seven').  STS analogue: Pasch has D = 0 (critical).
Usage: py shape_exponents.py
"""
import math, itertools
import numpy as np
from scipy.optimize import minimize
def h(x): return 0.0 if x <= 0 or x >= 1 else -x*math.log(x) - (1-x)*math.log(1-x)
def lC(a, b): return 0.0 if b <= 0 or b >= a else a*h(b/a)

def maxent(cells, N, eqs, ineqs, x0=None):
    """max -sum v ln(v/N) s.t. sum v = N, eqs: list of (coef, rhs) equalities, ineqs: (coef, rhs) meaning coef.v <= rhs."""
    m = len(cells)
    f = lambda v: float(np.sum(v*np.log(np.maximum(v, 1e-300)/N)))
    g = lambda v: np.log(np.maximum(v, 1e-300)/N) + 1
    cons = [{'type': 'eq', 'fun': lambda v: v.sum() - N, 'jac': lambda v: np.ones(m)}]
    for a, b in eqs: cons.append({'type': 'eq', 'fun': (lambda v, a=a, b=b: a @ v - b), 'jac': (lambda v, a=a: a)})
    for a, b in ineqs: cons.append({'type': 'ineq', 'fun': (lambda v, a=a, b=b: b - a @ v), 'jac': (lambda v, a=a: -a)})
    best = None
    rng = np.random.default_rng(1)
    for trial in range(6):
        v0 = rng.random(m) + 0.1; v0 *= N / v0.sum()
        r = minimize(f, v0, jac=g, constraints=cons, bounds=[(1e-12, N)]*m, method='SLSQP',
                     options={'maxiter': 2000, 'ftol': 1e-13})
        ok = r.success and all(c['fun'](r.x) > -1e-7 if c['type'] == 'ineq' else abs(c['fun'](r.x)) < 1e-7 for c in cons)
        if ok and (best is None or r.fun < best.fun): best = r
    return (-best.fun, best.x) if best is not None else (None, None)

def venn(r): return [frozenset(I) for j in range(r+1) for I in itertools.combinations(range(r), j)]

def qprime(t, N):
    c = N - 1; cells = venn(4)
    eqs = [(np.array([1.0 if i in I else 0 for I in cells]), c) for i in range(4)]
    sig = np.array([1.0 if len(I) <= 1 else 0 for I in cells])
    ineqs = [(sig, (3*t - N)/2)]
    for (a, b), (cc, d) in [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]:
        ineqs.append((sig + np.array([1.0 if I in (frozenset((a, b)), frozenset((cc, d))) else 0 for I in cells]), t))
    return maxent(cells, N, eqs, ineqs)

def pencil(t, N):
    c = N - 1; cells = [I for I in venn(3) if I]          # union = V
    eqs = [(np.array([1.0 if i in I else 0 for I in cells]), c) for i in range(3)]
    ineqs = [(np.array([-1.0 if len(I) == 3 else 0 for I in cells]), -(N - 2*t))]
    return maxent(cells, N, eqs, ineqs)

def triangle(t, N):
    c = N - 1; cells = [I for I in venn(3) if len(I) < 3]   # empty triple intersection
    eqs = [(np.array([1.0 if i in I else 0 for I in cells]), c) for i in range(3)]
    pr = [np.array([1.0 if I == frozenset(p) else 0 for I in cells]) for p in itertools.combinations(range(3), 2)]
    ineqs = [(p, (t + N - 2)/2) for p in pr] + [(-(pr[0]+pr[1]+pr[2]), -(3*N - 3 - t)/2)]
    return maxent(cells, N, eqs, ineqs)

CNT = [7, 28, 21, 7, 1]
def fano7(N):
    mean = 7*(N-1)/N; lo, hi = 1e-9, 1e9
    for _ in range(200):
        x = math.sqrt(lo*hi); den = sum(cc*x**j for j, cc in enumerate(CNT))
        mm = 3 + sum(j*cc*x**j for j, cc in enumerate(CNT))/den
        lo, hi = (x, hi) if mm < mean else (lo, x)
    return N*(math.log(den) - (mean - 3)*math.log(x))

if __name__ == "__main__":
    for t in (0.7501, 0.76, 0.78):
        print(f"t={t}:   N     w     gamma   Phi    Pool-Phi |  D_Q'     D_pencil  D_tri    D_fano7")
        lo, hi = 5*t - 2, 3 - t
        for i in range(1, 12):
            N = lo + (hi - lo)*i/12; c = N - 1; w = c - t
            g = lC(N - t, w); Phi = lC(N, t) - lC(c, t); Pool = lC(N - w, t)
            HQ, _ = qprime(t, N); HP, _ = pencil(t, N); HT, _ = triangle(t, N); H7 = fano7(N)
            fmt = lambda H, r: "   none " if H is None else f"{H - r*g - Phi:+8.4f}"
            print(f"     {N:.4f} {w:.4f} {g:.4f} {Phi:.4f} {Pool-Phi:+.4f} | {fmt(HQ,4)} {fmt(HP,3)} {fmt(HT,3)} {fmt(H7,7)}")
