"""Parallel driver for advsearch: one R1, many candidates (static screen in parallel), then jm.stage2 in parallel
on the statically invulnerable candidates with the most live mass.  usage: py run_adv.py R1csv nrand nproc tag"""
import sys, json, time, random
from multiprocessing import Pool
from advsearch import candidates, static_vals, T, S, SPEC, jm
def scr(item):
    key, m, o = item
    sv = static_vals(m, stop=T + 1e-6)
    ok = len(sv) == 4 and all(v is not None and v > T + 1e-6 for v in sv.values())
    return key, m, o, sv, ok
def st2(item):
    key, m, o, sv = item; t0 = time.time()
    res, info, it, _ = jm.stage2(S, m, o, T, SPEC, maxit=150, tl=100, wall=420)
    cert = [[{'%s%d' % k: v for k, v in P.items() if v > 0}, PO] for P, PO in info] if res == 'ADV' else None
    r2 = None
    if res == 'REQ': r2 = [{'%s%d' % k: v for k, v in info[0].items() if v > 1e-7}, info[1], info[2][0]]
    return key, sv, res, it, round(time.time() - t0), cert, r2
if __name__ == '__main__':
    r = [float(x) for x in sys.argv[1].split(',')]; nr = int(sys.argv[2]); NP = int(sys.argv[3]); tag = sys.argv[4]
    out = open('logs/adv_%s.jsonl' % tag, 'w'); t0 = time.time()
    cand = candidates(r, random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 0), nr)
    print('R1', r, 'candidates', len(cand), flush=True)
    with Pool(NP) as p:
        res = p.map(scr, cand, chunksize=4)
        good = [(k, m, o, sv) for k, m, o, sv, ok in res if ok]
        print('static-invulnerable', len(good), 'of', len(cand), round(time.time() - t0), 's', flush=True)
        good.sort(key=lambda g: -sum(g[1][c] for c in jm.L))
        for key, sv, rs, it, sec, cert, r2 in p.imap_unordered(st2, good[:2 * NP]):
            print('  M1', key, {k: round(v, 3) for k, v in sv.items()}, '->', rs, it, sec, 's', ('R2=%s' % r2 if r2 else ''), flush=True)
            out.write(json.dumps({'R1': r, 'M1': list(key), 'static': sv, 'res': rs, 'it': it, 'cert': cert, 'R2': r2}) + '\n'); out.flush()
    print('done', round(time.time() - t0), flush=True)
