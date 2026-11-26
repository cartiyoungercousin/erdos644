"""Depth-2 drop-frame probe of adversary states.  usage: py run_depth2.py states.jsonl nproc tag [nrand] [limit]
For each state (M1) and each of her candidate R2: does one of his candidate M2 refute R2 exactly?  Unrefuted R2
('THREAT') are logged with the best his candidates achieved."""
import sys, json, time, random
from multiprocessing import Pool
from depth2 import her_R2, his_M2, evaluate, refutes, C7
T = 12 - 0.002
def work(arg):
    li, st, nrand = arg; rng = random.Random(li)
    m1 = dict(zip(C7, st[:7])); o1 = st[7]; t0 = time.time()
    threats = []; n = 0
    for nm, r2 in her_R2(m1, o1, T, rng, nrand):
        n += 1; ok = False; best = None
        for m2, w in his_M2(m1, o1, r2, T, rng):
            U, vals = evaluate(m1, o1, m2, w, T)
            sc = min([U] + [v if v is not None else 0 for v in vals.values()]) if len(vals) == 5 else -1
            if best is None or sc > best[0]: best = (sc, U, vals, m2, w)
            if refutes(U, vals, T): ok = True; break
        if not ok:
            threats.append({'src': nm, 'R2': {'%s%d' % k: v for k, v in r2.items() if v > 1e-9},
                            'best_U': best[1] if best else None,
                            'best_vals': best[2] if best else None})
    return {'M1': st, 'nR2': n, 'threats': threats, 'sec': round(time.time() - t0)}
if __name__ == '__main__':
    rows = [json.loads(l) for l in open(sys.argv[1])]
    NP = int(sys.argv[2]); tag = sys.argv[3]; nr = int(sys.argv[4]) if len(sys.argv) > 4 else 20
    lim = int(sys.argv[5]) if len(sys.argv) > 5 else len(rows)
    items = [(i, r['M1'], nr) for i, r in enumerate(rows[:lim]) if r.get('M1')]
    out = open('logs/depth2_%s.jsonl' % tag, 'w'); t0 = time.time(); nth = 0
    with Pool(NP) as p:
        for i, res in enumerate(p.imap_unordered(work, items)):
            out.write(json.dumps(res) + '\n'); out.flush()
            nth += bool(res['threats'])
            print('[%ds] %d/%d M1 %s: %d R2 tried, %d unrefuted' % (time.time() - t0, i + 1, len(items),
                  [round(x, 3) for x in res['M1']], res['nR2'], len(res['threats'])), flush=True)
    print('done; states with threats', nth)
