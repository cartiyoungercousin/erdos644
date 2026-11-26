r"""Re-decide every 'ADV' state of the old certificate file with the SCIP master (scipy-HiGHS gave a false
infeasibility, see notes).  The old pattern list seeds the CEGAR.  Output: logs/cover_v3_a<alpha>_d<delta>.jsonl.
usage: py -3.14 reverify.py alpha delta nproc [first M1 only: comma list]"""
import sys, os, json, time
import multiprocessing as mp
import jm
AL, DE, NP = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
S = jm.sizes(AL); T = 12 - DE; HERE = os.path.dirname(os.path.abspath(__file__))
OLD = os.path.join(HERE, 'logs', 'cover_a%g_d%g.jsonl' % (AL, DE)); NEW = os.path.join(HERE, 'logs', 'cover_v3_a%g_d%g.jsonl' % (AL, DE))
def unkey(P): return {(k[:-1], int(k[-1])): v for k, v in P.items()}
def work(d):
    st = d['M1']; m1 = dict(zip(jm.C7, st[:7])); t0 = time.time()
    init = [(unkey(P), PO) for P, PO in d.get('cert', [])]
    res, info, it, _ = jm.stage2(S, m1, st[7], T, jm.SPEC, maxit=200, tl=170, init=init)
    out = {'M1': st, 'res': res, 'it': it, 'sec': round(time.time() - t0, 1), 'src': 'v3', 'seed': len(init)}
    if res == 'ADV': out['cert'] = [[{'%s%d' % k: v for k, v in P.items() if v > 0}, PO] for P, PO in info]
    if res == 'REQ': out['R2'] = [{'%s%d' % k: v for k, v in info[0].items() if v > 1e-7}, info[1], info[2][0]]
    return out
if __name__ == '__main__':
    done = set()
    if os.path.exists(NEW):
        for l in open(NEW): done.add(tuple(json.loads(l)['M1']))
    rows = [json.loads(l) for l in open(OLD)]
    rows = [d for d in rows if d['res'] == 'ADV' and tuple(d['M1']) not in done]
    if len(sys.argv) > 4:
        want = [float(x) for x in sys.argv[4].split(',')]; rows = [d for d in rows if d['M1'] == want]
    seen = set(); uniq = []
    for d in rows:
        if tuple(d['M1']) not in seen: seen.add(tuple(d['M1'])); uniq.append(d)
    print('%d states to re-verify' % len(uniq), flush=True); cnt = {}; t0 = time.time()
    with mp.Pool(NP) as pool, open(NEW, 'a') as f:
        for i, out in enumerate(pool.imap_unordered(work, uniq)):
            f.write(json.dumps(out) + '\n'); f.flush(); cnt[out['res']] = cnt.get(out['res'], 0) + 1
            if out['res'] != 'ADV': print('  NOT CONFIRMED', out['M1'], out['res'], out.get('R2'), flush=True)
            if (i + 1) % 50 == 0 or i + 1 == len(uniq): print('%d/%d %s %.0fs' % (i + 1, len(uniq), cnt, time.time() - t0), flush=True)
