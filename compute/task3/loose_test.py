r"""Task 3(1): saturation (Lemma 4) test for incidences (z, B) of an explicit family on V = 22 points.
(z, B) is saturated iff K' = (V - B) + {z} and at most six co-edges of the OTHER members cover all pairs {u, v}
(u = v allowed) of V; only pairs with an endpoint in D = B - {z} need the six.  SAT: x_K per member, at-most-6
(sequential counter), one clause per needed pair.  SAT answers give an explicit seven, re-checked by plain code
[computed exact]; UNSAT = loose [solver-only, CaDiCaL]; timeouts reported as UNKNOWN.
Usage: py -3.14 loose_test.py FAMILY.npy NSAMPLE SEED TLIMIT [out.jsonl]"""
import sys, json, time, numpy as np, threading
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
n = 22; FULL = (1 << n) - 1; nX = 12; Xm = (1 << nX) - 1
fam = [int(b) for b in np.load(sys.argv[1])]; ns = int(sys.argv[2]); seed = int(sys.argv[3]); tl = float(sys.argv[4])
outp = sys.argv[5] if len(sys.argv) > 5 else None
co = np.array([FULL & ~b for b in fam], dtype=np.int64); M = len(fam)
# pair -> members whose co-edge contains the pair
bit = [((co >> p) & 1).astype(bool) for p in range(n)]
def test(i, z):
    B = fam[i]; Kp = (FULL & ~B) | (1 << z); D = [p for p in range(n) if not Kp >> p & 1]
    pairs = [(u, v) for u in D for v in range(n) if v not in D or v >= u]
    cl = []
    for u, v in pairs:
        idx = np.nonzero(bit[u] & bit[v])[0]; idx = idx[idx != i]
        cl.append([int(t) + 1 for t in idx])
    card = CardEnc.atmost(lits=list(range(1, M + 1)), bound=6, top_id=M, encoding=EncType.seqcounter)
    s = Cadical153(bootstrap_with=cl + card.clauses)
    timer = threading.Timer(tl, s.interrupt); timer.start(); t0 = time.time()
    r = s.solve_limited(expect_interrupt=True); timer.cancel(); dt = time.time() - t0
    if r is None: s.delete(); return 'UNKNOWN', dt, None
    if r is False: s.delete(); return 'LOOSE', dt, None
    mdl = s.get_model(); s.delete()
    chosen = [t - 1 for t in mdl[:M] if t > 0]
    seven = [Kp] + [int(co[t]) for t in chosen]
    ok = len(chosen) <= 6 and all(any(K >> u & 1 and K >> v & 1 for K in seven) for u in range(n) for v in range(u, n))
    assert ok, "re-check failed"
    return 'SATURATED', dt, [fam[t] for t in chosen]
rng = np.random.default_rng(seed)
# stratify by class: profile of B and side of z
prof = lambda B: (bin(B & Xm).count('1'), bin(B >> nX).count('1'))
classes = {}
for i, B in enumerate(fam):
    for side in ('X', 'Y'):
        if (side == 'X' and B & Xm) or (side == 'Y' and B >> nX): classes.setdefault((prof(B), side), []).append(i)
f = open(outp, 'a') if outp else None
for key in sorted(classes):
    res = {}
    for _ in range(ns):
        i = int(rng.choice(classes[key])); B = fam[i]
        pts = [p for p in range(n) if B >> p & 1 and ((p < nX) == (key[1] == 'X'))]; z = int(rng.choice(pts))
        st, dt, cert = test(i, z); res[st] = res.get(st, 0) + 1
        if f: f.write(json.dumps({'B': B, 'z': z, 'status': st, 'sec': round(dt, 1), 'others': cert}) + "\n"); f.flush()
        print(f"  class {key} B={B} z={z}: {st} ({dt:.1f}s)", flush=True)
    print(f"class profile={key[0]} z in {key[1]}: {res}", flush=True)
