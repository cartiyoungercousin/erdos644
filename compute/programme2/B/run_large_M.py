r"""Whole pipeline at larger codimension (random columns, k = 200, n = 366, N = 1.83): Omegas by exact
meet-in-the-middle (weight <= 5), then B1 (reserved bases) and B1m (Lemma C* over all parts); exact verification."""
import sys, os, json, random, time
sys.path.insert(0, os.path.dirname(__file__))
from fam import coset_from_columns, omegas_mitm
from b1 import b1_construct, b1m_construct, check_seven
from core import evenise, verify_seven, popc
rng = random.Random(int(sys.argv[1]))
out = open(os.path.join(os.path.dirname(__file__), 'logs', f'largeM_s{sys.argv[1]}.jsonl'), 'w')
k, n = 200, 366
for M in [16, 20, 24, 28, 32] * 2:
    cols = [rng.getrandbits(M) for _ in range(n)]; alpha = rng.getrandbits(M) or 1
    cs0 = coset_from_columns(n, cols, M, alpha); cs = evenise(cs0, k)
    t0 = time.time(); Os = omegas_mitm(cs)
    rec = dict(M=M, k=k, n=n, cells=len(set(cols)))
    if Os is None: rec['fail'] = 'no Omegas <= 5'; print(rec); continue
    rec['w'] = [popc(O) for O in Os]
    for name, fn in (('B1', b1_construct), ('B1m', b1m_construct)):
        rep = {}; B = fn(cs, k, Os, rng=rng, report=rep)
        ok = B is not None and check_seven(n, cs0.H, cs0.alpha, k, B)[0] and verify_seven(cs, k, B)[0]
        rec[name] = ok; rec[name + '_fail'] = rep.get('fail'); rec['m_min'] = rep.get('m_min', rec.get('m_min'))
    rec['sec'] = round(time.time() - t0, 1)
    out.write(json.dumps(rec) + '\n'); out.flush(); print(rec, flush=True)
