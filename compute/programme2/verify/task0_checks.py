"""Independent exact checks for PROGRAMME_2 Task 0 (Lemma 2, Theorem 3, Lemma 5, Corollary 7, Lemma 8,
heavy atoms, (Sigma)(a)/(c) in F2 form).  Integer / Fraction arithmetic only (LPs: float solve, exact
re-check).  Usage: py -3.14 task0_checks.py [seed]
"""
import itertools, random, sys
from fractions import Fraction as Fr
import numpy as np
from scipy.optimize import linprog
from pysat.solvers import Solver

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
R = random.Random(seed)
LINES = [(0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5)]   # Fano plane on points 0..6
PENCIL = {p: [l for l in range(7) if p in LINES[l]] for p in range(7)}
popc = lambda x: bin(x).count('1')
fails = []
def check(cond, msg):
    if not cond: fails.append(msg); print('FAIL', msg)

def has_2transversal(sets, n):
    for a in range(n):
        for b in range(a, n):
            m = (1 << a) | (1 << b)
            if all(s & m for s in sets): return True
    return False
def is_transversal(M, H): return all(B & M for B in H)
def L_of(chi, l, n): return sum(1 << x for x in range(n) if chi[x] in LINES[l])

# ---------------------------------------------------------------- Lemma 2
cnt = 0
for _ in range(4000):
    n = R.randint(4, 10)
    H = list({R.randrange(1, 1 << n) for _ in range(R.randint(1, 25))})
    chi = [R.randrange(7) for _ in range(n)]
    Ls = [L_of(chi, l, n) for l in range(7)]
    if any(is_transversal(L, H) for L in Ls): continue
    seven = [next(B for B in H if not B & Ls[l]) for l in range(7)]
    cnt += 1
    check(not has_2transversal(seven, n), 'Lemma 2')
print('Lemma 2: instances with no transversal line:', cnt)

# ---------------------------------------------------------------- Theorem 3: greedy balancing bound
def greedy(y):
    load = [Fr(0)] * 7; col = [0] * len(y)
    for x in sorted(range(len(y)), key=lambda x: -y[x]):   # any order works for the bound; LPT order
        c = min(range(7), key=lambda c: load[c]); col[x] = c; load[c] += y[x]
    return col, load
def greedy_any(y, order):
    load = [Fr(0)] * 7
    for x in order:
        c = min(range(7), key=lambda c: load[c]); load[c] += y[x]
    return load
for _ in range(3000):
    n = R.randint(1, 40)
    kind = R.randrange(3)
    if kind == 0: y = [Fr(R.randint(0, 20), 20) for _ in range(n)]
    elif kind == 1: y = [Fr(1, n)] * n
    else: y = [Fr(R.randint(5, 9), 10)] * R.randint(1, 3) + [Fr(1, 100)] * n
    order = list(range(len(y))); R.shuffle(order)
    load = greedy_any(y, order)
    Y, mx = sum(y), max(y)
    check(max(load) <= Y / 7 + mx, 'greedy class bound')
    check(all(sum(load[p] for p in l) <= 3 * Y / 7 + 3 * mx for l in LINES), 'greedy line bound')

# Theorem 3 end-to-end on families where the hypothesis holds (tau*_b by exact LP over all transversals)
def tau_b_star(H, n):
    trans = [M for M in range(1, 1 << n) if is_transversal(M, H)]
    minimal = [M for M in trans if not any((M & ~(1 << i)) in set(trans) for i in range(n) if M >> i & 1)]
    A = np.array([[-(M >> i & 1) for i in range(n)] for M in minimal], float)
    r = linprog(np.ones(n), A_ub=A, b_ub=-np.ones(len(minimal)), bounds=[(0, None)] * n, method='highs')
    y = [Fr(v).limit_denominator(1000) for v in r.x]
    ok = all(sum(y[i] for i in range(n) if M >> i & 1) >= 1 for M in minimal)
    return y if ok else None
e2e = 0
for n, k in [(9, 3), (10, 3), (11, 3), (12, 3), (12, 4), (13, 4)]:
    allk = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)]
    for rep in range(3):
        H = allk if rep == 0 else [B for B in allk if R.random() < 0.97]
        y = tau_b_star(H, n)
        if y is None or sum(y) + 7 * max(y) >= Fr(7, 3): continue
        col, load = greedy(y)
        Ls = [sum(1 << x for x in range(n) if col[x] in LINES[l]) for l in range(7)]
        check(all(not is_transversal(L, H) for L in Ls), 'Thm3: a line is a transversal')
        seven = [next(B for B in H if not B & L) for L in Ls]
        check(not has_2transversal(seven, n), 'Thm3: seven has 2-transversal')
        e2e += 1
print('Theorem 3 end-to-end instances (hypothesis satisfied):', e2e)
# consequence for pool families: K_{k+tau-1}^{(k)} with tau > 3(n+7)/7  <=>  tau > 3k/4 + 9/2
for k in range(1, 200):
    for tau in range(1, k + 2):
        n = k + tau - 1
        check((7 * tau > 3 * (n + 7)) == (4 * tau > 3 * k + 18), 'pool consequence')

# ---------------------------------------------------------------- Lemma 5
def s_p(Bs, p):
    v = 0
    for l in PENCIL[p]: v ^= Bs[l]
    return v
for _ in range(20000):
    n = R.randint(1, 14)
    chi = [R.randrange(7) for _ in range(n)]
    Rl = [sum(1 << x for x in range(n) if chi[x] not in LINES[l]) for l in range(7)]
    Bs = [Rl[l] & R.randrange(1 << n) for l in range(7)]
    j = [sum(Bs[l] >> x & 1 for l in range(7)) for x in range(n)]
    lhs = sum(popc(s_p(Bs, p)) for p in range(7))
    mid = sum(jx * (4 - jx) for jx in j)
    U = 0
    for b in Bs: U |= b
    rhs = 3 * (4 * popc(U) - sum(popc(b) for b in Bs))
    check(lhs == mid, 'pencil identity'); check(mid <= rhs, 'pencil inequality')
    check(max(j) <= 4, 'j_x <= 4')
# zero slack: j_x in {0,4}  -> all s_p = 0 and {0} + seven sets is a 3-dim subspace (if all nonempty)
sub_ok = 0
for _ in range(3000):
    n = R.randint(1, 14)
    chi = [R.randrange(7) for _ in range(n)]
    Bs = [0] * 7
    for x in range(n):
        if R.random() < 0.7:
            for l in range(7):
                if chi[x] not in LINES[l]: Bs[l] |= 1 << x
    U = 0
    for b in Bs: U |= b
    check(4 * popc(U) == sum(popc(b) for b in Bs), 'zero slack construction')
    check(all(s_p(Bs, p) == 0 for p in range(7)), 'zero slack => s_p = 0')
    if all(Bs):
        S = set(Bs) | {0}
        check(len(S) == 8 and all((a ^ b) in S for a in S for b in S), 'subspace of dim 3')
        sub_ok += 1
print('Lemma 5 zero-slack subspace instances:', sub_ok)
# without B_l in R_l the identity fails (control)
Bs = [1] * 7
check(sum(popc(s_p(Bs, p)) for p in range(7)) == 7 and 7 * (4 - 7) < 0, 'control')
# pencil shape (b): three k-sets, empty common intersection: wt(x1+x2+x3) = 2|U| - 3k
for _ in range(5000):
    n = R.randint(3, 16); k = R.randint(1, n)
    xs = [sum(1 << i for i in R.sample(range(n), k)) for _ in range(3)]
    if xs[0] & xs[1] & xs[2]: continue
    U = xs[0] | xs[1] | xs[2]
    check(popc(xs[0] ^ xs[1] ^ xs[2]) == 2 * popc(U) - 3 * k, 'pencil shape identity')

# ---------------------------------------------------------------- Corollary 7 / Fano-type good sevens by SAT
def fano_seven_sat(H, n):
    """Exact: exists chi and B_l in H with B_l cap L_l = empty?  Returns (chi, Bs) or None."""
    s = Solver(name='cadical153'); v = {}
    def V(key):
        if key not in v: v[key] = len(v) + 1
        return v[key]
    for x in range(n):
        s.add_clause([V(('c', x, p)) for p in range(7)])
    for l in range(7):
        s.add_clause([V(('b', l, i)) for i in range(len(H))])
        for i, B in enumerate(H):
            for x in range(n):
                if B >> x & 1:
                    for p in LINES[l]: s.add_clause([-V(('b', l, i)), -V(('c', x, p))])
    if not s.solve(): return None
    m = set(z for z in s.get_model() if z > 0)
    chi = [next(p for p in range(7) if V(('c', x, p)) in m) for x in range(n)]
    Bs = [H[next(i for i in range(len(H)) if V(('b', l, i)) in m)] for l in range(7)]
    return chi, Bs
def span(gens):
    S = {0}
    for g in gens: S |= {s ^ g for s in S}
    return S
cor7_tests = cor7_app = 0
for _ in range(400):
    n = R.randint(6, 11); k = R.randint(2, n - 2)
    C = span([R.randrange(1 << n) for _ in range(R.randint(1, n - 1))])
    a = R.randrange(1 << n)
    if a in C: continue
    coset = [a ^ c for c in C]
    rho = min(popc(z) for z in coset)
    H = [z for z in coset if popc(z) == k]
    if not H: continue
    res = fano_seven_sat(H, n)
    cor7_tests += 1
    if 7 * rho > 3 * (4 * n - 7 * k):
        cor7_app += 1
        check(res is None, 'Cor 7 violated')
    if res:
        chi, Bs = res
        Ls = [L_of(chi, l, n) for l in range(7)]
        check(all(not B & L for B, L in zip(Bs, Ls)), 'sat model')
        check(not has_2transversal(Bs, n), 'Fano seven not good')
        tot = sum(popc(s_p(Bs, p)) for p in range(7))
        check(7 * rho <= tot <= 3 * (4 * n - 7 * k), 'Cor 7 chain')
print('Cor 7 random coset families:', cor7_tests, 'with hypothesis 7rho > 3(4n-7k):', cor7_app)

# FKW: X (|X| = 4m), Y; edges = k-sets with |A cap X| odd (k = 4m). Fano-type good seven via class sizes.
def comps(total, parts):
    if parts == 1: yield (total,); return
    for i in range(total + 1):
        for r in comps(total - i, parts - 1): yield (i,) + r
def fkw_fano(m, ny):
    k, nx = 4 * m, 4 * m
    ycomp = {}
    for yc in comps(ny, 7):
        Yl = tuple(ny - sum(yc[p] for p in LINES[l]) for l in range(7))
        ycomp[Yl] = yc
    ymax = list(ycomp.keys())
    for xc in comps(nx, 7):
        need = []
        okx = True
        for l in range(7):
            Xl = nx - sum(xc[p] for p in LINES[l])
            j = Xl if Xl % 2 else Xl - 1
            if j < 1: okx = False; break
            need.append(k - j)
        if not okx: continue
        for Yl in ymax:
            if all(Yl[l] >= need[l] for l in range(7)): return xc, ycomp[Yl]
    return None
for m in (1, 2, 3):
    r1 = fkw_fano(m, 3 * m + 1); r2 = fkw_fano(m, 3 * m + 2)
    print(f'FKW m={m}: n=7m+1 Fano-type good seven: {r1 is not None};  n=7m+2: {r2 is not None}', r2)
    check(r1 is None, 'FKW 7m+1 has Fano seven')
    check(r2 is not None, 'FKW 7m+2 claim')

# ---------------------------------------------------------------- Lemma 8
def min_r_cover(H, n, k):
    Hs = H
    for r in range(0, n - k + 1):
        if all(any(B & ~S == 0 for B in Hs) for S in (sum(1 << i for i in c) for c in itertools.combinations(range(n), k + r))):
            return r
    return None
l8 = 0
for _ in range(300):
    n = R.randint(5, 11); k = R.randint(2, n - 2)
    allk = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)]
    if len(allk) > 330: continue
    p = R.choice([0.3, 0.5, 0.8, 1.0])
    H = [B for B in allk if R.random() < p]
    if len(H) < 3: continue
    r = min_r_cover(H, n, k)
    if r is None or 2 * n < 3 * k + 2 * r + 2: continue
    best = min(popc(a ^ b ^ c) for a, b, c in itertools.combinations(H, 3))
    best_rep = min(popc(a ^ b ^ c) for a, b, c in itertools.combinations_with_replacement(H, 3))
    check(best_rep <= 2 * r + 1, f'Lemma 8 (multiset) n={n} k={k} r={r}')
    if best > 2 * r + 1: print('  Lemma 8 holds only with a repeated member:', n, k, r, best)
    l8 += 1
print('Lemma 8 instances:', l8)
# adversarial: greedy deletion keeping the (k+r)-cover property, maximise the min triple sum
worst = []
for (n, k, r) in [(8, 4, 1), (9, 4, 1), (9, 5, 1), (10, 4, 2), (10, 6, 1), (11, 6, 1), (11, 5, 2)]:
    if 2 * n < 3 * k + 2 * r + 2: continue
    allk = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)]
    big = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k + r)]
    for trial in range(4):
        H = allk[:]; R.shuffle(H)
        for B in H[:]:
            H2 = [C for C in H if C != B]
            if all(any(C & ~S == 0 for C in H2) for S in big): H = H2
        best_rep = min(popc(a ^ b ^ c) for a, b, c in itertools.combinations_with_replacement(H, 3))
        check(best_rep <= 2 * r + 1, f'Lemma 8 adversarial {n},{k},{r}')
        worst.append((n, k, r, len(H), best_rep))
print('Lemma 8 adversarial (n,k,r,|H|,min triple sum):', worst)
# second part: codeword of weight w >= k + r  =>  rho <= w - k
for _ in range(400):
    n = R.randint(6, 12); k = R.randint(2, n - 3)
    C = span([R.randrange(1 << n) for _ in range(R.randint(2, n - 1))])
    a = R.randrange(1 << n)
    if a in C: continue
    coset = [a ^ c for c in C]
    H = [z for z in coset if popc(z) == k]
    if not H: continue
    rho = min(popc(z) for z in coset)
    r = min_r_cover(H, n, k)
    if r is None: continue
    for c in C:
        if popc(c) >= k + r: check(rho <= popc(c) - k, 'Lemma 8 part 2')

# ---------------------------------------------------------------- heavy atoms
# (i) K_10^(6): (7,2) (7 co-edges of size 4 cover <= 42 < 45 pairs), tau = 5 > 3k/4, tau*_b = 2 < 7/3
n, k = 10, 6
H = [sum(1 << i for i in c) for c in itertools.combinations(range(n), k)]
y = tau_b_star(H, n)
print('K_10^(6): tau*_b =', sum(y), ' tau =', min(popc(M) for M in range(1 << n) if is_transversal(M, H)),
      ' pair count 7*C(4,2) =', 7 * 6, '< C(10,2) =', 45)
check(sum(y) == 2, 'K10 tau_b')
# (ii) y alone: three atoms 49/100 + light mass 4/5 (atoms <= 1/100): every 7-colouring has a line of mass >= 1
def min_max_line(h, L):
    # min over light loads c >= 0, sum c = L of max_l sum_{p in l}(h_p + c_p)  (fractional: a lower bound
    # for every actual colouring of the light points)
    c = np.zeros(8); c[7] = 1
    A = [[1 if p in LINES[l] else 0 for p in range(7)] + [-1] for l in range(7)]
    b = [-sum(h[p] for p in LINES[l]) for l in range(7)]
    r = linprog(c, A_ub=np.array(A, float), b_ub=np.array(b, float), A_eq=np.array([[1] * 7 + [0]], float),
                b_eq=[L], bounds=[(0, None)] * 8, method='highs')
    return r.fun
best = min(min_max_line([sum(Fr(49, 100) for a in pl if a == p) for p in range(7)], 0.8)
           for pl in itertools.product(range(7), repeat=3))
print('three atoms 0.49 + light 0.8 (total 2.27 < 7/3): best fractional max line =', round(best, 6))
check(best >= 1 - 1e-9, 'heavy obstruction')

# ---------------------------------------------------------------- (Sigma)(a): Q' in F2 form
# cells: member-pattern P subset of [4] (which of B1..B4 contain the point), integer masses; |B_i| = k
pats = list(range(16))
for _ in range(20000):
    b = {P: R.randint(0, 6) for P in pats}
    sizes = [sum(b[P] for P in pats if P >> i & 1) for i in range(4)]
    if len(set(sizes)) != 1: continue
    k = sizes[0]; n = sum(b.values()); T = R.randint(0, n)
    g = b[0]
    wt4 = sum(b[P] for P in pats if popc(P) % 2)                       # wt(x1+x2+x3+x4)
    sigma = sum(b[P] for P in pats if popc(P) >= 3)                    # in >= 3 members
    W = sum(b[P] for P in pats if popc(P) == 1) + 2 * b[0] + sum(b[P] for P in pats if popc(P) == 3)
    check(W == wt4 + 2 * g, 'W = wt + 2g')
    check(W == 2 * n - 4 * k + 2 * sigma, 'W = 2N - 4 + 2 sigma')
    q1 = 2 * sigma <= 3 * T - n
    check(q1 == (wt4 + 2 * g <= n + 3 * T - 4 * k), "Q' first condition in F2 form")
    for (i, j), (u, v) in [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]:
        cm = b[(1 << i) | (1 << j)] + b[(1 << u) | (1 << v)]
        # F2: points with x_i = x_j, x_u = x_v, x_i != x_u
        cm2 = sum(b[P] for P in pats if (P >> i & 1) == (P >> j & 1) and (P >> u & 1) == (P >> v & 1)
                  and (P >> i & 1) != (P >> u & 1))
        check(cm == cm2, 'matching cell')
    # Theorem Q tau-distribution exists iff Q'
    cms = [b[3] + b[12], b[5] + b[10], b[9] + b[6]]
    big = sum(b[P] for P in pats if popc(P) <= 1)    # co-type size >= 3  (u3 + u4)
    thmQ = all(c + sigma <= T for c in cms) and sum(T - c - sigma for c in cms) >= big
    check(thmQ == (q1 and all(c + sigma <= T for c in cms)), "Q' <=> Theorem Q")

# ---------------------------------------------------------------- (Sigma)(c): Theorem T in F2 form
tt = 0
for _ in range(20000):
    n = R.randint(3, 16); k = R.randint(1, n); T = R.randint(0, n)
    xs = [sum(1 << i for i in R.sample(range(n), k)) for _ in range(3)]
    full = (1 << n) - 1
    if xs[0] | xs[1] | xs[2] != full: continue      # kappa = empty
    K = [full ^ x for x in xs]
    a = popc(K[0] & K[1] & ~K[2]); bb = popc(K[0] & K[2] & ~K[1]); d = popc(K[1] & K[2] & ~K[0])
    e = [popc(K[i] & ~K[(i + 1) % 3] & ~K[(i + 2) % 3]) for i in range(3)]
    gg = popc(full & ~(K[0] | K[1] | K[2]))
    cells = (a + e[2] + gg <= T and bb + e[1] + gg <= T and d + e[0] + gg <= T and sum(e) <= T)
    closed = (2 * a <= T + n - 2 * k and 2 * bb <= T + n - 2 * k and 2 * d <= T + n - 2 * k
              and 2 * (a + bb + d) >= 3 * n - 3 * k - T)
    f2 = all(popc(full ^ xs[i] ^ xs[j]) <= T for i, j in [(0, 1), (0, 2), (1, 2)]) and \
         popc(full ^ xs[0] ^ xs[1] ^ xs[2]) <= T
    check(cells == closed == f2, 'Theorem T forms')
    S = [full ^ xs[0] ^ xs[1], full ^ xs[0] ^ xs[2], full ^ xs[1] ^ xs[2]]
    check(S[0] ^ S[1] ^ S[2] == full, 'S4+S5+S6 = 1')
    tt += 1
print('Theorem T form instances:', tt)
print('TOTAL FAILURES:', len(fails))
