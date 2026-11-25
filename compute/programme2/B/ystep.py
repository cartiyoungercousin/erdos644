r"""The Y-step in isolation (the crux of B for many classes): random columns of rank e on a ground set of size
sum(m), seven region sizes m_p; does the sequential multipart Lemma C* (b1.multi_lemma_c, three steps) find a
labelling v: V'' -> F2^3 - 0 with |v^-1(p)| = m_p and every bit-class a codeword?  Each success is re-checked
exactly (the three sums are recomputed).  usage: ystep.py seed"""
import sys, os, random, json
sys.path.insert(0, os.path.dirname(__file__))
from b1 import multi_lemma_c, LAB, rank

def trial(rng, m, M):
    mv = {v: m + rng.randint(-2, 2) for v in range(1, 8)}; mv[0] = 0
    # parity: each bit-class must have even size (C even); fix by adjusting region 7
    for i in range(3):
        if sum(c for v, c in mv.items() if v >> i & 1) % 2:
            pass
    tot = [sum(c for v, c in mv.items() if v >> i & 1) for i in range(3)]
    # make all three bit-class sizes even by adjusting single-bit regions
    for i in range(3):
        if tot[i] % 2: mv[1 << i] += 1
    N = sum(mv.values())
    cols = [rng.getrandbits(M) | (1 << M) for _ in range(N)]    # parity bit set: an even code
    e = rank([c ^ cols[0] for c in cols])
    bits = [0] * N
    for i in range(3):
        parts = []
        for pref in range(1 << i):
            U = [x for x in range(N) if bits[x] == pref]; rng.shuffle(U)
            a = sum(c for v, c in mv.items() if v & ((1 << i) - 1) == pref and v >> i & 1)
            parts.append((U, a))
        Qs = multi_lemma_c(parts, 0, cols)
        if Qs is None: return dict(m=m, M=M, e=e, ok=False, step=i + 1)
        for Q in Qs:
            for x in Q: bits[x] |= 1 << i
    for i in range(3):
        s = 0
        for x in range(N):
            if bits[x] >> i & 1: s ^= cols[x]
        assert s == 0
    cnt = {v: bits.count(v) for v in range(8)}
    assert all(cnt[v] == mv[v] for v in range(8))
    return dict(m=m, M=M, e=e, ok=True)

if __name__ == '__main__':
    seed = int(sys.argv[1]); rng = random.Random(seed)
    out = open(os.path.join(os.path.dirname(__file__), 'logs', f'ystep_s{seed}.jsonl'), 'w')
    for m in (20, 40):
        for frac in (0.5, 1.0, 1.5, 2.0, 2.5, 2.8, 3.0, 3.2, 3.5, 4.0):
            M = int(frac * m)
            res = [trial(rng, m, M) for _ in range(10)]
            okc = sum(r['ok'] for r in res)
            fails = sorted({r.get('step') for r in res if not r['ok']} - {None})
            rec = dict(m=m, M=M, ratio=frac, ok=okc, of=len(res), fail_steps=fails, e=[r['e'] for r in res][:3])
            out.write(json.dumps(rec) + '\n'); out.flush(); print(rec, flush=True)
