r"""Consequence test (coordinator's reading of Task 1(c)): Corollary 5 sets U_z in 2-cell profile families.
[SAT answers: computed exact (explicit sets re-checked by plain code). UNSAT: solver-only (CaDiCaL), controls in
logs/uz_*.log.]
Family: V = A + Y (|A| = nA, |Y| = nY; points 0..nA-1 are A), co-edges = all sets whose profile (|K&A|, |K&Y|) is in P.
For a co-edge K of profile p and a point z not in K (z in A or z in Y), Corollary 5 asks for <= 6 co-edges K_1..K_6 with
  z in U := U(K_1..K_6),  U inside K + {z},  |U| >= T + 1,  U inside no co-edge (profile of U dominated by no q in P).
By symmetry the answer depends only on (p, side of z). U is encoded exactly: g_uv <=> no K_i contains {u, v};
x_u <=> some g_uv. Same symmetry breaking as sat_profile.py.
Usage: py -3.14 uz_profile.py '<json>'  json = {nA, nY, T, P: [[a,b],...], K: [a,b], side: 'A'|'Y', tag}"""
import sys, json, itertools, time
from pysat.solvers import Cadical153
from pysat.card import ITotalizer, CardEnc, EncType
cfg = json.loads(sys.argv[1])
nA, nY, T, P = cfg['nA'], cfg['nY'], cfg['T'], [tuple(p) for p in cfg['P']]
n = nA + nY; Acell = list(range(nA)); Ycell = list(range(nA, n)); free = 6
ka, kb = cfg['K']; side = cfg['side']
K = set(Acell[:ka]) | set(Ycell[:kb])
z = Acell[ka] if side == 'A' else Ycell[kb]
assert z not in K and tuple(cfg['K']) in P
Kp = K | {z}
top = [0]
def new():
    top[0] += 1; return top[0]
m = [[new() for p in range(n)] for b in range(free)]
cls = []
def lex_ge(Av, Bv):
    e = None
    for i, (a, b) in enumerate(zip(Av, Bv)):
        cls.append([a, -b] if e is None else [-e, a, -b])
        if i == len(Av) - 1: break
        e2 = new()
        cls.extend([[a, b, e2], [-a, -b, e2]] if e is None else [[-e, a, b, e2], [-e, -a, -b, e2]]); e = e2
def card_is(lits, t, guard):
    L = len(lits)
    up = ITotalizer(lits=lits, ubound=L, top_id=top[0]); cls.extend(up.cnf.clauses); top[0] = max(top[0], up.top_id)
    dn = ITotalizer(lits=[-l for l in lits], ubound=L, top_id=top[0]); cls.extend(dn.cnf.clauses); top[0] = max(top[0], dn.top_id)
    if t > L: cls.append([-guard]); return
    if t < L: cls.append([-guard, -up.rhs[t]])
    if t > 0: cls.append([-guard, -dn.rhs[L - t]])
for b in range(free):
    sel = [new() for _ in P]; cls.append(sel)
    for s1, s2 in itertools.combinations(sel, 2): cls.append([-s1, -s2])
    for s, pr in zip(sel, P):
        card_is([m[b][p] for p in Acell], pr[0], s); card_is([m[b][p] for p in Ycell], pr[1], s)
g = {}; x = [new() for p in range(n)]
for u in range(n):
    for v in range(u, n):
        gv = new(); g[(u, v)] = g[(v, u)] = gv
        ws = []
        for b in range(free):
            cls.append([-gv, -m[b][u]] if u == v else [-gv, -m[b][u], -m[b][v]])
            if u == v: ws.append(m[b][u])
            else:
                w = new(); cls.extend([[-w, m[b][u]], [-w, m[b][v]]]); ws.append(w)
        cls.append([gv] + ws)  # not covered -> g
for u in range(n):
    cls.append([-x[u]] + [g[(u, v)] for v in range(n)])
    for v in range(n): cls.append([-g[(u, v)], x[u]])
for u in range(n):
    if u not in Kp: cls.append([-x[u]])  # U inside K + {z}
cls.append([x[z]])
c1 = CardEnc.atleast(lits=x, bound=T + 1, top_id=top[0], encoding=EncType.seqcounter); cls.extend(c1.clauses); top[0] = max(top[0], c1.nv)
# U inside no co-edge: for every q in P, |U & A| >= q0 + 1 or |U & Y| >= q1 + 1
upA = ITotalizer(lits=[x[p] for p in Acell], ubound=nA, top_id=top[0]); cls.extend(upA.cnf.clauses); top[0] = max(top[0], upA.top_id)
upY = ITotalizer(lits=[x[p] for p in Ycell], ubound=nY, top_id=top[0]); cls.extend(upY.cnf.clauses); top[0] = max(top[0], upY.top_id)
dnA = ITotalizer(lits=[-x[p] for p in Acell], ubound=nA, top_id=top[0]); cls.extend(dnA.cnf.clauses); top[0] = max(top[0], dnA.top_id)
dnY = ITotalizer(lits=[-x[p] for p in Ycell], ubound=nY, top_id=top[0]); cls.extend(dnY.cnf.clauses); top[0] = max(top[0], dnY.top_id)
for q0, q1 in P:
    lits = []
    if q0 + 1 <= nA: lits.append(-dnA.rhs[nA - q0 - 1])  # |U&A| >= q0+1  <=>  #nonU in A <= nA-q0-1
    if q1 + 1 <= nY: lits.append(-dnY.rhs[nY - q1 - 1])
    cls.append(lits)
for b in range(free - 1): lex_ge([m[b][p] for p in range(n)], [m[b + 1][p] for p in range(n)])
sig = {}
for p in range(n): sig.setdefault((p < nA, p in K, p == z), []).append(p)
for ps in sig.values():
    for p, q in zip(ps, ps[1:]): lex_ge([m[b][p] for b in range(free)], [m[b][q] for b in range(free)])
t0 = time.time()
with Cadical153(bootstrap_with=cls) as s:
    sat = s.solve(); model = set(l for l in s.get_model() if l > 0) if sat else None
dt = time.time() - t0; tag = cfg.get('tag', '')
if not sat:
    print(f"[{tag}] UNSAT: no U_z for K profile {tuple(cfg['K'])}, z in {side} ({dt:.1f}s) [solver-only]"); sys.exit()
blocks = [{p for p in range(n) if m[b][p] in model} for b in range(free)]
U = {u for u in range(n) if any(not any(u in B and v in B for B in blocks) for v in range(n))}
prof = lambda S: (len(S & set(Acell)), len(S & set(Ycell)))
ok = all(prof(B) in P for B in blocks) and z in U and U <= Kp and len(U) >= T + 1
ok &= not any(prof(U)[0] <= q0 and prof(U)[1] <= q1 for q0, q1 in P)
print(f"[{tag}] SAT: U_z exists for K profile {tuple(cfg['K'])}, z in {side} ({dt:.1f}s); re-check {ok}; "
      f"|U| = {len(U)}, profile(U) = {prof(U)}, K_i profiles {[prof(B) for B in blocks]}")
