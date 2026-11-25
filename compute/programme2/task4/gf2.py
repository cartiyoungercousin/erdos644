r"""F2 helpers for PROGRAMME_2 Task 4.  Sets are int bitmasks; + is XOR; wt is popcount."""
import numpy as np, itertools
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import csr_matrix

_T16 = np.array([bin(i).count('1') for i in range(1 << 16)], dtype=np.uint8)
def pc(a):
    """popcount of int64 array (values < 2^48) or python int."""
    if isinstance(a, (int, np.integer)): return bin(int(a)).count('1')
    a = np.asarray(a, dtype=np.int64)
    return (_T16[a & 0xFFFF].astype(np.int16) + _T16[(a >> 16) & 0xFFFF] + _T16[(a >> 32) & 0xFFFF]).astype(np.int16)

def reduced_basis(vecs, n):
    """Reduced row echelon basis (list of ints, pivot = highest set bit) of span(vecs); vecs int64 array."""
    D = np.unique(np.asarray(vecs, dtype=np.int64)); D = D[D != 0]; basis = []
    for bit in range(n - 1, -1, -1):
        if len(D) == 0: break
        sel = ((D >> bit) & 1).astype(bool)
        if not sel.any(): continue
        piv = D[np.argmax(sel)]; D = np.where(sel, D ^ piv, D); D = D[D != 0]; basis.append(int(piv))
    # make fully reduced
    basis.sort(reverse=True)
    for i in range(len(basis)):
        hb = basis[i].bit_length() - 1
        for j in range(len(basis)):
            if j != i and (basis[j] >> hb) & 1: basis[j] ^= basis[i]
    return basis

def reduce_by(a, basis):
    for b in basis:
        if (a >> (b.bit_length() - 1)) & 1: a ^= b
    return a

def annihilator(basis, n):
    """basis of {h : h.b = 0 for all b in span} (parity checks)."""
    piv = {b.bit_length() - 1: b for b in basis}; out = []
    for f in range(n):
        if f in piv: continue
        h = 1 << f
        for p, b in piv.items():
            if (b >> f) & 1: h |= 1 << p
        out.append(h)
    return out

def coset_min_weight(a, basis, n, enum_limit=26):
    """exact min weight of a + span(basis). Returns (rho, witness)."""
    a = reduce_by(a, basis); d = len(basis)
    if a == 0: return 0, 0
    if d <= enum_limit:
        d1 = min(d, 13); A = np.zeros(1, dtype=np.int64)
        for b in basis[:d1]: A = np.concatenate([A, A ^ b])
        best = (10**9, 0); rest = basis[d1:]
        comb = [a]
        for b in rest: comb = comb + [c ^ b for c in comb]
        for c in comb:
            v = A ^ c; w = pc(v); i = int(np.argmin(w))
            if w[i] < best[0]: best = (int(w[i]), int(v[i]))
        return best
    H = annihilator(basis, n); s = [bin(h & a).count('1') & 1 for h in H]; m = len(H)
    rows = np.zeros((m, n + m))
    for i, h in enumerate(H):
        for j in range(n):
            if (h >> j) & 1: rows[i, j] = 1
        rows[i, n + i] = -2
    cons = LinearConstraint(csr_matrix(rows), lb=np.array(s, float), ub=np.array(s, float))
    c = np.concatenate([np.ones(n), np.zeros(m)])
    r = milp(c, constraints=cons, integrality=np.ones(n + m), bounds=Bounds(np.zeros(n + m), np.concatenate([np.ones(n), np.full(m, n)])))
    x = sum(1 << j for j in range(n) if r.x[j] > 0.5)
    return int(round(r.fun)), x

def fwht(f):
    f = f.astype(np.int32).copy(); n = f.size.bit_length() - 1
    for i in range(n):
        v = f.reshape(-1, 2, 1 << i); a = v[:, 0, :].copy(); b = v[:, 1, :]
        v[:, 0, :] = a + b; v[:, 1, :] = a - b
    return f
