"""General one-request adaptive closure of a good triple (no lemma list): she requests U (any masses on the six cells),
he answers K (any masses, traces on E, F, G in the spectrum S), she finishes with three static blocks on E,F,G,K
(exact MILP over all labellings, Lemma 2.4 candidate pairs) or discards one of E,F,G and finishes the good triple left
with four static blocks (t*_+, all 715 classes).  Units of k, nu = infinity.
Every atom he can make nonempty is treated as nonempty (0+ costs him nothing at first order).
She: structured + random search over U.  He: grid + random + coordinate ascent over K.  [heuristic both sides:
a found K is a genuine spoiler for that U; "no U found" is not a proof.]
usage: py -3.14 depth1.py t x y z [G] [Ssets]"""
import sys, os, itertools, random, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'beat78'))

LAB = [s for s in range(1, 8)]                      # nonempty subsets of {0,1,2}
ATOMS = ['X1', 'X0', 'Y1', 'Y0', 'Z1', 'Z0', 'E1', 'E0', 'F1', 'F0', 'G1', 'G0']
AI = {a: i for i, a in enumerate(ATOMS)}
Gm = ['Y1', 'Y0', 'Z1', 'Z0', 'G1', 'G0']; Fm = ['X1', 'X0', 'Z1', 'Z0', 'F1', 'F0']; Em = ['X1', 'X0', 'Y1', 'Y0', 'E1', 'E0']
CAND = set()
for a in Gm: CAND.add(frozenset(('X1', a)))
for a in Fm: CAND.add(frozenset(('Y1', a)))
for a in Em: CAND.add(frozenset(('Z1', a)))
CAND |= {frozenset(('X0', 'G1')), frozenset(('Y0', 'F1')), frozenset(('Z0', 'E1'))}
CAND = [tuple(sorted(p)) for p in CAND if len(p) == 2]

def static3(mass, present):
    """min max load of 3 blocks covering all candidate pairs of E,F,G,K; mass/present dicts over ATOMS"""
    nA, nL = len(ATOMS), 7
    nb = nA * nL; nv = 2 * nb + 1                     # b, w, tau
    bi = lambda a, s: AI[a] * nL + (s - 1)
    wi = lambda a, s: nb + AI[a] * nL + (s - 1)
    rows, lo, hi = [], [], []
    def add(coefs, l, h):
        r = np.zeros(nv)
        for j, c in coefs: r[j] += c
        rows.append(r); lo.append(l); hi.append(h)
    need = {a: present[a] and any(present[c] for (p, q) in CAND for (b_, c) in ((p, q), (q, p)) if b_ == a)
            for a in ATOMS}
    for a in ATOMS:
        m = mass[a] if need[a] else 0.0
        add([(wi(a, s), 1) for s in LAB], m, m)
        for s in LAB: add([(wi(a, s), 1), (bi(a, s), -m)], -np.inf, 0)
        if need[a]: add([(bi(a, s), 1) for s in LAB], 1, np.inf)
    for (a, c) in CAND:
        if not (present[a] and present[c]): continue
        for s in LAB:
            for s2 in LAB:
                if s & s2 == 0: add([(bi(a, s), 1), (bi(c, s2), 1)], -np.inf, 1)
    for gblk in range(3):
        add([(wi(a, s), 1) for a in ATOMS for s in LAB if s >> gblk & 1] + [(nv - 1, -1)], -np.inf, 0)
    A = np.array(rows)
    cost = np.zeros(nv); cost[-1] = 1
    integ = np.zeros(nv); integ[:nb] = 1
    ub = np.full(nv, np.inf); ub[:nb] = 1
    res = milp(cost, constraints=LinearConstraint(A, lo, hi), integrality=integ, bounds=Bounds(np.zeros(nv), ub),
               options={'disp': False, 'mip_rel_gap': 1e-9})
    return res.fun if res.status == 0 else np.inf

_T = None
def tplus(x):
    global _T
    import tstar
    return tstar.tstar(tuple(max(0.0, v) for v in x))

def value(cells, U, K):
    """her best finish after answer K to request U (both dicts over X,Y,Z,E,F,G)"""
    x, y, z = cells; tot = {'X': x, 'Y': y, 'Z': z, 'E': 1 - x - y, 'F': 1 - x - z, 'G': 1 - y - z}
    mass, present = {}, {}
    for c in 'XYZEFG':
        mass[c + '1'] = K[c]; mass[c + '0'] = tot[c] - K[c]
        present[c + '1'] = (tot[c] - U[c]) > 1e-12            # he may put a point there
        present[c + '0'] = True if c in 'XYZ' else (tot[c] - K[c] > 1e-12 or True)
    best = static3(mass, present)
    # discards: drop one of E,F,G; the remaining triple with K is good iff the corresponding triple cell is empty
    if not present['X1']: best = min(best, tplus((x, K['Y'] + K['E'], K['Z'] + K['F'])))
    if not present['Y1']: best = min(best, tplus((y, K['X'] + K['E'], K['Z'] + K['G'])))
    if not present['Z1']: best = min(best, tplus((z, K['X'] + K['F'], K['Y'] + K['G'])))
    return best

def traces(K):
    return (K['X'] + K['Y'] + K['E'], K['X'] + K['Z'] + K['F'], K['Y'] + K['Z'] + K['G'])

def spoil(cells, U, t, inS, rng, G=48, tries=400):
    """search for an answer K with value > t; returns (K, value) or None"""
    x, y, z = cells; tot = {'X': x, 'Y': y, 'Z': z, 'E': 1 - x - y, 'F': 1 - x - z, 'G': 1 - y - z}
    cap = {c: max(0.0, tot[c] - U[c]) for c in 'XYZEFG'}
    def snap(v): return np.floor(v * G + 1e-9) / G
    def legal(K):
        if sum(K.values()) > 1 + 1e-12: return False
        return all(inS(tr) and tr < 1 - 1e-12 for tr in traces(K))
    best = None
    # structured candidates: fill cells greedily in random priority orders
    orders = list(itertools.permutations('XYZEFG'))
    rng.shuffle(orders)
    cand = []
    for o in orders[:tries]:
        K = {c: 0.0 for c in 'XYZEFG'}; room = 1.0
        for c in o:
            v = snap(min(cap[c], room * rng.choice([1, 1, 0.5, 0.25]))); K[c] = v; room -= v
        cand.append(K)
    for K in cand:
        # repair traces into S by lowering private-part masses
        for _ in range(3):
            tr = traces(K)
            for i, c in enumerate('EFG'):
                while not inS(traces(K)[i]) and K[c] > 0: K[c] = max(0.0, K[c] - 1.0 / G)
        if not legal(K): continue
        v = value(cells, U, K)
        if v > t + 1e-9: return K, v
        if best is None or v > best[1]: best = (K, v)
    return None if best is None else (best[0], best[1], 'max-found')

if __name__ == '__main__':
    t, x, y, z = map(float, sys.argv[1:5])
    rng = random.Random(1)
    inS = lambda v: True
    # demo: the request of Lemma 4.2 (avoid X,Y,Z and t-S of P_F)
    U = {'X': x, 'Y': y, 'Z': z, 'E': 0, 'F': t - x - y - z, 'G': 0}
    print(spoil((x, y, z), U, t, inS, rng))
