r"""Driver: enumerate class-A-continuation first requests R1 on grid h (units k/14), answer each with candidate M1's
(oracle1 with several drop weightings), and decide the stage-2 game exactly by CEGAR (jm.stage2).  Checkpointed jsonl.
R1: live cells X,Y,A,B on grid h with the remainder of t put into one live cell; dead cells Ep,Fd,Gd requested 0,
half or full (half = nearest grid point below |c|/2).  R2 is CONTINUOUS (stronger for her than any grid).
usage: py -3.14 run_stage.py alpha h delta nproc [sample N] [spec|nospec]"""
import sys, os, json, time, itertools, random
import numpy as np
import multiprocessing as mp
import jm

AL, H, DE, NP = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
SAMPLE = int(sys.argv[5]) if len(sys.argv) > 5 else 0
SPECN = sys.argv[6] if len(sys.argv) > 6 else 'spec'
SPEC = jm.SPEC if SPECN == 'spec' else jm.NOSPEC
S = jm.sizes(AL); T = 12 - DE
HERE = os.path.dirname(os.path.abspath(__file__))

WEIGHTS = [None,                                              # plain min drops
           {'X': 1, 'Y': 1, 'A': 1.3, 'B': 1.3},              # prefer dropping hubs
           {'X': 1.3, 'Y': 1.3, 'A': 1, 'B': 1},              # prefer dropping A/B
           {'X': 1, 'Y': 1.3, 'A': 1.3, 'B': 1}, {'X': 1.3, 'Y': 1, 'A': 1, 'B': 1.3}]


def grid(m):
    v = [round(x, 9) for x in np.arange(0, m + 1e-9, H)]
    if m - v[-1] > 1e-9: v.append(m)
    return v


def requests():
    reqs = set()
    dopt = {c: sorted({0.0, S[c], np.floor(S[c] / 2 / H) * H}) for c in ('Ep', 'Fd', 'Gd')}
    for dv in itertools.product(dopt['Ep'], dopt['Fd'], dopt['Gd']):
        for free in range(4):
            oth = [i for i in range(4) if i != free]
            for vals in itertools.product(*[grid(S[jm.L[i]]) for i in oth]):
                rem = T - sum(vals) - sum(dv)
                if rem < -1e-9: continue
                r = [0.0] * 7
                for i, v in zip(oth, vals): r[i] = v
                r[free] = min(rem, S[jm.L[free]]); r[4:] = dv
                if sum(r) < T - 1e-9 and r[free] < S[jm.L[free]] - 1e-9: continue
                reqs.add(tuple(round(x, 6) for x in r))
    return sorted(reqs)


def work(r):
    r1 = dict(zip(jm.C7, r)); t0 = time.time(); out = {'R1': r, 'tries': []}
    seen = set()
    for w in WEIGHTS:
        o = jm.oracle1(S, r1, SPEC, w=w, wpad={'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3})
        if o is None: out['verdict'] = 'NO_M1'; break
        m1, o1 = o
        key = tuple(round(m1[c], 5) for c in jm.C7) + (round(o1, 5),)
        if key in seen: continue
        seen.add(key)
        res, info, it = jm.stage2(S, m1, o1, T, SPEC, maxit=150)
        out['tries'].append({'M1': [m1[c] for c in jm.C7], 'o1': o1, 'res': res, 'it': it,
                             'npat': len(info) if res != 'REQ' else 0,
                             'R2': ({'%s%d' % k: v for k, v in info[0].items() if v > 1e-7}, info[1], info[2][0]) if res == 'REQ' else None})
        if res == 'ADV': out['verdict'] = 'ADV'; break
    else:
        out['verdict'] = 'OPEN' if any(t['res'] == '?' for t in out['tries']) else 'REQ_ALL_M1'
    out['sec'] = round(time.time() - t0, 2)
    return out


if __name__ == '__main__':
    reqs = requests()
    tag = 'a%g_h%g_d%g_%s' % (AL, H, DE, SPECN) + ('_s%d' % SAMPLE if SAMPLE else '')
    fn = os.path.join(HERE, 'logs', 'stage_%s.jsonl' % tag)
    done = set()
    if os.path.exists(fn):
        for line in open(fn):
            try: done.add(tuple(json.loads(line)['R1']))
            except Exception: pass
    if SAMPLE:
        random.seed(1); reqs = random.sample(reqs, min(SAMPLE, len(reqs)))
    todo = [r for r in reqs if tuple(r) not in done]
    print('alpha=%g t=%g h=%g %s: %d requests, %d done, %d to do' % (AL, T, H, SPECN, len(reqs), len(done), len(todo)), flush=True)
    t0 = time.time(); cnt = {}
    with mp.Pool(NP) as pool, open(fn, 'a') as f:
        for i, out in enumerate(pool.imap_unordered(work, todo, chunksize=1)):
            f.write(json.dumps(out) + '\n'); f.flush()
            cnt[out['verdict']] = cnt.get(out['verdict'], 0) + 1
            if out['verdict'] != 'ADV':
                print('  NON-ADV', out['verdict'], out['R1'], [(tr['res'], tr['it']) for tr in out['tries']], flush=True)
            if (i + 1) % 50 == 0 or i + 1 == len(todo):
                print('%d/%d  %s  %.0fs' % (i + 1, len(todo), cnt, time.time() - t0), flush=True)
