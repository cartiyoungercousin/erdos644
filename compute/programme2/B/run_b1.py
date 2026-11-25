r"""Stress test of Theorem B1 on many-class coset families.  usage: run_b1.py seed count [k n]
Every success is checked by b1.check_seven (original rows) and by task3 core.verify_seven (evenised rows)."""
import sys, os, json, random, time
sys.path.insert(0, os.path.dirname(__file__))
from fam import gen, coset_from_columns, omegas, cover_cert
from b1 import b1_construct, check_seven
from core import evenise, verify_seven, popc

def one(rng, k, n, kind, M, q, cellpool):
    cols, R, extra = gen(kind, n, M, rng, q=q, cellpool=cellpool)
    alpha = rng.getrandbits(M) or 1
    cs0 = coset_from_columns(n, cols, R, alpha, kind)       # planted rows have alpha bit 0
    cs = evenise(cs0, k)
    Os = omegas(cs, cs.r)
    rec = dict(kind=kind, k=k, n=n, M=M, q=q, cellpool=cellpool)
    if Os is None: rec['fail'] = 'no Omegas'; return rec
    rec['w'] = [popc(O) for O in Os]
    cert = cover_cert(cs, k) if cs.r <= 16 else {}
    rec.update(cert)
    rep = {}
    B = b1_construct(cs, k, Os, rng=rng, report=rep)
    rec.update(rep)
    if B is not None:
        ok1, why1 = check_seven(n, cs0.H, cs0.alpha, k, B)
        ok2, why2 = verify_seven(cs, k, B)
        rec['verified'] = ok1 and ok2
        if not (ok1 and ok2): rec['why'] = (why1, why2)
    return rec

if __name__ == '__main__':
    seed, count = int(sys.argv[1]), int(sys.argv[2])
    k = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    n = int(sys.argv[4]) if len(sys.argv) > 4 else 720
    rng = random.Random(seed)
    out = open(os.path.join(os.path.dirname(__file__), 'logs', f'b1_s{seed}_k{k}_n{n}.jsonl'), 'w')
    for it in range(count):
        kind = rng.choice(['rand', 'rand', 'mix', 'series', 'sparse'])
        M = rng.choice([6, 8, 10, 12, 14])
        q = rng.randint(1, 12) if kind in ('series', 'sparse') else 0
        cellpool = rng.choice([5, 20, 80]) if kind == 'mix' else 0
        t0 = time.time()
        rec = one(rng, k, n, kind, M, q, cellpool)
        rec['sec'] = round(time.time() - t0, 1)
        out.write(json.dumps(rec) + '\n'); out.flush()
        print(it, {a: rec.get(a) for a in ('kind', 'M', 'q', 'cells', 'e', 'X', 'X0', 'u', 'm_min', 'T_cert', 'fail', 'verified', 'sec')}, flush=True)
