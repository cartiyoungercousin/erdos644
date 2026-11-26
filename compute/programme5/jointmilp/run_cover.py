r"""Cover driver.  Every first request R1 (class-A continuation, grid h, units k/14) must be refuted by SOME legal
answer M1 whose stage-2 game is an adversary win (jm.stage2 -> 'ADV').  An M1 refutes every R1 it avoids
(m1_c + r1_c <= |c| for all cells; its traces do not depend on R1), so we refute a small greedy set of M1 states.
Candidate M1 states: his canonical min-drop answer to each R1 (several drop weightings).  Previously refuted states
(any grid, same alpha/delta) are reused.  R2 is continuous.  Checkpoint: logs/cover_<tag>.jsonl (one line per state).
usage: py -3.14 run_cover.py alpha h delta nproc [poolsize]"""
import sys, os, json, time, itertools
import numpy as np
import multiprocessing as mp
import jm

AL, H, DE, NP = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
POOLN = int(sys.argv[5]) if len(sys.argv) > 5 else 16
SPEC = jm.SPEC
S = jm.sizes(AL); T = 12 - DE; SV = np.array([S[c] for c in jm.C7])
HERE = os.path.dirname(os.path.abspath(__file__))
WP = {'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3}
WEIGHTS = [None, {'X': 1, 'Y': 1, 'A': 1.3, 'B': 1.3}, {'X': 1.3, 'Y': 1.3, 'A': 1, 'B': 1},
           {'X': 1, 'Y': 1.3, 'A': 1.3, 'B': 1}, {'X': 1.3, 'Y': 1, 'A': 1, 'B': 1.3}]


def grid(m):
    v = [round(x, 9) for x in np.arange(0, m + 1e-9, H)]
    if m - v[-1] > 1e-9: v.append(m)
    return v


def requests():
    """maximal grid requests: live cells on grid h, one live cell takes the remainder of t; dead cells 0/half/full"""
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


def cand(r):
    out = []
    for w in WEIGHTS:
        o = jm.oracle1(S, dict(zip(jm.C7, r)), SPEC, w=w, wpad=WP)
        if o is None: continue
        m1, o1 = o
        out.append(tuple(round(m1[c], 6) for c in jm.C7) + (round(o1, 6),))
    return out


def cand_vol(r):
    """voluntary drops: his canonical answer with d of one live cell replaced by fresh outside points (pad room)"""
    o = jm.oracle1(S, dict(zip(jm.C7, r)), SPEC, wpad=WP)
    if o is None: return []
    m1, o1 = o; out = []
    for c in jm.L:
        for d in (0.25, 0.5, 1.0):
            if m1[c] < d - 1e-9: continue
            mm = dict(m1); mm[c] -= d
            st = tuple(round(mm[x], 6) for x in jm.C7) + (round(o1 + d, 6),)
            if legal_m1(st): out.append(st)
    return out


def work(args):
    st, pool = args
    m1 = dict(zip(jm.C7, st[:7])); o1 = st[7]; t0 = time.time()
    res, info, it, newrel = jm.stage2(S, m1, o1, T, SPEC, maxit=120, pool=pool, tl=150)
    out = {'M1': list(st), 'res': res, 'it': it, 'sec': round(time.time() - t0, 1)}
    if res == 'ADV': out['cert'] = [[{'%s%d' % k: v for k, v in P.items() if v > 0}, PO] for P, PO in info]
    if res in ('REQ', 'ORACLE_FAIL'): out['R2'] = [{'%s%d' % k: v for k, v in info[0].items() if v > 1e-7}, info[1], info[2][0]]
    return out, newrel


def legal_m1(st):
    m = dict(zip(jm.C7, st[:7]))
    if abs(sum(st) - 14) > 1e-4: return False
    return all(jm.in_spec(sum(m[c] for c in cs), SPEC, 1e-5) for cs in jm.MEM.values())


if __name__ == '__main__':
    tag = 'a%g_d%g' % (AL, DE)
    fn = os.path.join(HERE, 'logs', 'cover_%s.jsonl' % tag)
    logf = open(os.path.join(HERE, 'logs', 'cover_%s_h%g.log' % (tag, H)), 'a')
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); logf.write(s + '\n'); logf.flush()
    reqs = np.array(requests()); t0 = time.time()
    P('alpha=%g beta=%g t=%g grid h=%g: %d first requests' % (AL, 14 - AL, T, H, len(reqs)))
    done = {}
    if os.path.exists(fn):
        for line in open(fn):
            d = json.loads(line); done[tuple(d['M1'])] = d['res']
    with mp.Pool(NP) as pool:
        cl = pool.map(cand, [tuple(r) for r in reqs], chunksize=50)
    states = sorted({s for c in cl for s in c} | set(done))
    assert all(legal_m1(s) for s in states)
    M = np.array([s[:7] for s in states])
    cov = np.zeros((len(M), len(reqs)), bool)
    for i in range(0, len(M), 100):
        cov[i:i + 100] = np.all(M[i:i + 100, None, :] + reqs[None, :, :] <= SV + 1e-6, axis=2)
    P('%d candidate M1 states (%.0fs); every request avoided by its own candidates: %s' %
      (len(states), time.time() - t0, bool(cov.any(0).all())))
    left = np.ones(len(reqs), bool)
    for i, s in enumerate(states):
        if done.get(s) == 'ADV': left &= ~cov[i]
    tried = {s for s, v in done.items() if v in ('ADV', 'REQ')}
    P('already refuted by checkpoint: %d requests; left %d' % ((~left).sum(), left.sum()))
    relpool = {}; stats = {}
    def run_loop(pool, f):
        global left
        while left.any():
            g = (cov & left).sum(1)
            order = [i for i in np.argsort(-g, kind='stable') if g[i] > 0 and states[i] not in tried]
            if not order: break
            batch = []; mask = left.copy()
            for i in order:                            # greedy batch: pick states covering distinct requests
                gi = (cov[i] & mask).sum()
                if gi >= max(1, g[order[0]] // 4) or len(batch) < 2:
                    batch.append(i); mask &= ~cov[i]
                if len(batch) >= NP: break
            for out, newrel in pool.imap_unordered(work, [(states[i], []) for i in batch]):
                f.write(json.dumps(out) + '\n'); f.flush()
                s_ = tuple(out['M1']); tried.add(s_); stats[out['res']] = stats.get(out['res'], 0) + 1
                if out['res'] == 'ADV': left &= ~cov[states.index(s_)]
                else: P('  state', s_, '->', out['res'], out.get('R2'))
            P('batch of %d done: %s; requests left %d; %.0fs' % (len(batch), stats, left.sum(), time.time() - t0))
    with mp.Pool(NP) as pool, open(fn, 'a') as f:
        run_loop(pool, f)
        if left.any():
            P('phase 2: voluntary-drop candidates for %d uncovered requests' % left.sum())
            extra = pool.map(cand_vol, [tuple(r) for r in reqs[left]])
            new = sorted({st for c in extra for st in c} - set(states))
            if new:
                Mn = np.array([st[:7] for st in new])
                covn = np.all(Mn[:, None, :] + reqs[None, :, :] <= SV + 1e-6, axis=2)
                states.extend(new); cov = np.vstack([cov, covn])
                P('  %d new candidate states' % len(new))
                run_loop(pool, f)
    P('FINAL: requests not refuted: %d of %d' % (left.sum(), len(reqs)))
    for r in reqs[left][:50]: P('  UNREFUTED R1', list(r))
    json.dump([list(r) for r in reqs[left]], open(os.path.join(HERE, 'logs', 'unrefuted_%s_h%g.json' % (tag, H)), 'w'))
