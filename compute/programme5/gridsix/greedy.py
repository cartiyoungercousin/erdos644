"""Greedy cover of the first requests that lost all their certified E-frame ADV states to the static drop-one
frames: for each still-unrefuted R1 (largest first) search a new M1 (static-invulnerable and stage2-ADV) and add it.
usage: py greedy.py unrefuted.json nproc tag [nrand]   ->  logs/greedy_<tag>.jsonl (states found), .out"""
import sys, json, time, random
import numpy as np
from multiprocessing import Pool
from run_adv import scr, st2
from advsearch import candidates, jm, S
SV = np.array([S[c] for c in jm.C7])
if __name__ == '__main__':
    reqs = np.array(json.load(open(sys.argv[1]))); NP = int(sys.argv[2]); tag = sys.argv[3]
    nr = int(sys.argv[4]) if len(sys.argv) > 4 else 600
    order = np.argsort(-reqs.sum(1)); left = np.ones(len(reqs), bool)
    out = open('logs/greedy_%s.jsonl' % tag, 'a'); t0 = time.time(); fails = []
    def P(*a): print(*a, flush=True)
    with Pool(NP) as p:
        for idx in order:
            if not left[idx]: continue
            r = [float(x) for x in reqs[idx]]
            found = None
            for seed in range(3):
                cand = candidates(r, random.Random(seed), nr)
                res = p.map(scr, cand, chunksize=4)
                good = [(k, m, o, sv) for k, m, o, sv, ok in res if ok]
                good.sort(key=lambda g: -sum(g[1][c] for c in jm.L))
                for key, sv, rs, it, sec, cert, r2 in p.imap_unordered(st2, good[:NP]):
                    if rs == 'ADV' and found is None:
                        found = {'R1': r, 'M1': list(key), 'static': sv, 'res': rs, 'it': it, 'cert': cert}
                if found: break
            if found:
                out.write(json.dumps(found) + '\n'); out.flush()
                m = np.array(found['M1'][:7])
                cov = np.all(m[None, :] + reqs <= SV + 1e-6, axis=1)
                left &= ~cov
                P('[%ds] R1 %s -> M1 %s static %s ; covers %d ; left %d' % (time.time() - t0, r, found['M1'],
                  {k: round(v, 3) for k, v in found['static'].items()}, cov.sum(), left.sum()))
            else:
                left[idx] = False; fails.append(r)
                P('[%ds] R1 %s -> NO M1 FOUND (static-ok candidates tried: see run_adv)' % (time.time() - t0, r))
    json.dump(fails, open('logs/greedy_%s_fails.json' % tag, 'w'))
    P('done; fails', len(fails))
