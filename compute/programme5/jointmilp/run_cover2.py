r"""Cover driver v2 (memory-light, richer adversary candidates).  Same certificate file as run_cover.py:
logs/cover_a<alpha>_d<delta>.jsonl (one line per decided M1; 'ADV' lines carry the pattern certificate).
An M1 refutes every R1 it avoids (m1_c + r1_c <= |c|).  Candidate M1 for an uncovered R1, in order of tries:
  canon : his min-drop answer (5 drop weightings), pads from outside preferred;
  vol   : canon with d in {.25,.5,1} of one live cell replaced by outside points (Lemma Phi escape);
  box   : his min-drop answer to the enlarged request min(|c|, R1 + eta) (eta = .05, .15): covers a box of R1's.
modes:  grid h   -- all maximal requests on grid h (units k/14), as run_cover.py
        cont     -- repeatedly ask an MILP for a request (any reals, |R1| <= t) avoided by no refuted state
usage: py -3.14 run_cover2.py alpha delta nproc grid h | cont [rounds]"""
import sys, os, json, time, itertools
import numpy as np
import multiprocessing as mp
import jm

AL, DE, NP, MODE = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
S = jm.sizes(AL); T = 12 - DE; SV = np.array([S[c] for c in jm.C7]); SPEC = jm.SPEC
HERE = os.path.dirname(os.path.abspath(__file__))
WP = {'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3}
WEIGHTS = [None, {'X': 1, 'Y': 1, 'A': 1.3, 'B': 1.3}, {'X': 1.3, 'Y': 1.3, 'A': 1, 'B': 1},
           {'X': 1, 'Y': 1.3, 'A': 1.3, 'B': 1}, {'X': 1.3, 'Y': 1, 'A': 1, 'B': 1.3}]
FN = os.path.join(HERE, 'logs', 'cover_v3_a%g_d%g.jsonl' % (AL, DE))   # SCIP-verified certificates
EPSR = 1e-5


def key(m1, o1): return tuple(round(m1[c], 6) for c in jm.C7) + (round(o1, 6),)


def legal(st):
    m = dict(zip(jm.C7, st[:7]))
    return abs(sum(st) - 14) < 1e-4 and min(st) >= -1e-9 and all(
        jm.in_spec(sum(m[c] for c in cs), SPEC, 1e-6) for cs in jm.MEM.values())


def avoids(st, r): return all(st[i] + r[i] <= SV[i] + 1e-6 for i in range(7))


def cands(r):
    """candidate M1 for request r, in try order, each avoiding r"""
    out = []
    def add(st):
        if st not in out and legal(st) and avoids(st, r): out.append(st)
    canon = None
    for w in WEIGHTS:
        o = jm.oracle1(S, dict(zip(jm.C7, r)), SPEC, w=w, wpad=WP)
        if o is None: continue
        add(key(*o)); canon = canon or o
    for eta in (0.05, 0.15):
        rr = {c: min(S[c], r[i] + eta) for i, c in enumerate(jm.C7)}
        o = jm.oracle1(S, rr, SPEC, wpad=WP)
        if o is not None: add(key(*o))
    if canon:
        m1, o1 = canon
        for c in jm.L:
            for d in (0.25, 0.5, 1.0):
                if m1[c] >= d - 1e-9:
                    mm = dict(m1); mm[c] -= d; add(key(mm, o1 + d))
    return out


def biggest_box(arg):
    """for one escaping request: his answers to R1 + eta (eta descending, so the box it refutes is as large as
    possible), then canonical / voluntary-drop answers; decide each until one is ADV.  Returns decided lines."""
    r, known = arg
    outs = []; seen = set(known)
    order = []
    o0 = jm.oracle1(S, dict(zip(jm.C7, r)), SPEC, wpad=WP)
    m0 = o0[0] if o0 else {c: 0.0 for c in jm.C7}
    for eta in (2.0, 1.0, 0.5, 0.25, 0.1, 0.03, 0.01):
        for keepfrac in (0.5, 0.0):     # 0.5: never enlarge into the last half of what his answer keeps of a live cell
            rr = {c: min(S[c], r[i] + eta, (S[c] - keepfrac * m0[c]) if (c in jm.L and m0[c] > 1e-9) else S[c])
                  for i, c in enumerate(jm.C7)}
            rr = {c: max(rr[c], r[i]) for i, c in enumerate(jm.C7)}
            for w in WEIGHTS[:3]:
                o = jm.oracle1(S, rr, SPEC, w=w, wpad=WP)
                if o is not None: order.append(key(*o))
    # drop tiny live remnants entirely (a box that reaches the whole cell), singly and all together
    if o0:
        tiny = [c for c in jm.L if 0 < m0[c] < 0.3]
        for sub in ([[c] for c in tiny] + ([tiny] if len(tiny) > 1 else [])):
            mm = dict(m0); d = sum(mm[c] for c in sub)
            for c in sub: mm[c] = 0.0
            order.insert(0, key(mm, o0[1] + d))
    order += cands(r)
    for st in order:
        if st in seen or not legal(st) or not avoids(st, r): continue
        seen.add(st)
        out = decide(st); outs.append(out)
        if out['res'] == 'ADV': break
    return outs


def decide(st):
    m1 = dict(zip(jm.C7, st[:7])); t0 = time.time()
    res, info, it, _ = jm.stage2(S, m1, st[7], T, SPEC, maxit=200, tl=120, wall=float(os.environ.get('WALL', '200')))
    out = {'M1': list(st), 'res': res, 'it': it, 'sec': round(time.time() - t0, 1), 'src': 'v2'}
    if res == 'ADV': out['cert'] = [[{'%s%d' % k: v for k, v in P.items() if v > 0}, PO] for P, PO in info]
    if res == 'REQ': out['R2'] = [{'%s%d' % k: v for k, v in info[0].items() if v > 1e-7}, info[1], info[2][0]]
    return out


def load():
    adv, other = [], {}
    if os.path.exists(FN):
        for line in open(FN):
            d = json.loads(line); s = tuple(d['M1'])
            if d['res'] == 'ADV': adv.append(s)
            else: other[s] = d['res']
    return adv, other


def covered_mask(adv, reqs):
    if not adv: return np.zeros(len(reqs), bool)
    M = np.array([s[:7] for s in adv]); out = np.zeros(len(reqs), bool)
    for i in range(0, len(reqs), 2000):
        R = reqs[i:i + 2000]
        out[i:i + 2000] = np.any(np.all(M[:, None, :] + R[None, :, :] <= SV + 1e-6, axis=2), axis=0)
    return out


def grid_requests(H):
    def grid(m):
        v = [round(x, 9) for x in np.arange(0, m + 1e-9, H)]
        if m - v[-1] > 1e-9: v.append(m)
        return v
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
    return np.array(sorted(reqs))


def pareto(adv):
    """Pareto-minimal states (a state avoiding fewer requests than another is redundant)"""
    M = np.array([s_[:7] for s_ in adv]); keep = []
    order = np.argsort(M.sum(1))
    for i in order:
        if not any(np.all(M[j] <= M[i] + 1e-9) for j in keep): keep.append(i)
    return [adv[i] for i in keep]


def escaping(adv, obj=None, seed=0):
    """A request (reals, |R1| <= t) avoided by no state, or None if none exists.
    State i avoids R1 iff R1 lies in the box prod_c [0, |c| - m1_ic]; boxes are down-sets, so it suffices to search
    R1 whose coordinates are 0 or a box threshold + EPSR.  Pure 0/1 model solved exactly by CP-SAT:
    z[c,l] = 'R1_c reaches level l' (monotone in l), every box needs one cell above its threshold, and the level
    increments (rounded DOWN to 1e-7, i.e. in her favour) must fit in t.  A returned R1 is re-checked directly."""
    from ortools.sat.python import cp_model
    SC = 10 ** 7
    lev = {}
    for c_i, c in enumerate(jm.C7):
        th = sorted({round(S[c] - st[c_i] + EPSR, 9) for st in adv if st[c_i] > EPSR and S[c] - st[c_i] + EPSR <= S[c] + 1e-12})
        lev[c] = th
    md = cp_model.CpModel(); z = {}
    for c in jm.C7:
        for l in range(len(lev[c])):
            z[c, l] = md.NewBoolVar('')
            if l: md.AddImplication(z[c, l], z[c, l - 1])
    import bisect
    for st in adv:
        lits = []
        for c_i, c in enumerate(jm.C7):
            if st[c_i] <= EPSR: continue
            th = S[c] - st[c_i] + EPSR
            l = bisect.bisect_left(lev[c], round(th, 9) - 1e-12)
            if l < len(lev[c]): lits.append(z[c, l])
        if not lits: return None          # this state avoids every request
        md.AddBoolOr(lits)
    cost = []
    for c in jm.C7:
        prev = 0.0
        for l, v in enumerate(lev[c]):
            cost.append((int(np.floor((v - prev) * SC)), z[c, l])); prev = v
    md.Add(sum(w * x for w, x in cost) <= int(np.floor(T * SC)) + 1)
    if obj is not None:
        md.Maximize(sum(int(1000 * obj[i]) * z[c, l] for i, c in enumerate(jm.C7) for l in range(len(lev[c]))))
    sv = cp_model.CpSolver(); sv.parameters.max_time_in_seconds = 160; sv.parameters.num_workers = 4
    sv.parameters.random_seed = seed
    stt = sv.Solve(md)
    if stt == cp_model.INFEASIBLE: return None
    if stt not in (cp_model.OPTIMAL, cp_model.FEASIBLE): return 'TIMEOUT'
    rr = []
    for c in jm.C7:
        top = [lev[c][l] for l in range(len(lev[c])) if sv.Value(z[c, l])]
        rr.append(max(top) if top else 0.0)
    rr = tuple(rr)
    if sum(rr) > T + 1e-6:                 # rounding slack used: shave the largest coordinate's excess
        return 'ROUNDING'
    assert not any(avoids(st, rr) for st in adv), 'escape check failed'
    return rr


def canon_only(r):
    """tier-1 candidates: canonical answers, and canonical answers to enlarged requests (they cover a box)"""
    out = []
    reqs_ = [dict(zip(jm.C7, r))] + [{c: min(S[c], r[i] + eta) for i, c in enumerate(jm.C7)} for eta in (0.1, 0.25, 0.5)]
    for j, rr in enumerate(reqs_):
        for w in (WEIGHTS if j == 0 else WEIGHTS[:1]):
            o = jm.oracle1(S, rr, SPEC, w=w, wpad=WP)
            if o is not None:
                k = key(*o)
                if k not in out and legal(k) and avoids(k, r): out.append(k)
    return out


def greedy_round(pool, f, reqs, left, states, adv, other, P, t0, tagr):
    """greedy: decide the untried states covering most uncovered requests, NP*2 per batch"""
    M = np.array([s_[:7] for s_ in states]) if states else np.zeros((0, 7))
    tried = np.array([(s_ in other) or (s_ in adv) for s_ in states], bool)
    while left.any() and len(states):
        idx = np.where(left)[0]; R = reqs[idx]; cnt = np.zeros(len(states), int)
        for i in range(0, len(states), 500):
            cnt[i:i + 500] = np.all(M[i:i + 500, None, :] + R[None, :, :] <= SV + 1e-6, axis=2).sum(1)
        cnt[tried] = 0
        if cnt.max() == 0: break
        order = np.argsort(-cnt, kind='stable'); batch = []; mask = np.ones(len(idx), bool)
        for j in order:
            if cnt[j] == 0 or len(batch) >= 2 * NP: break
            cv = np.all(M[j][None, :] + R <= SV + 1e-6, axis=1)
            if (cv & mask).sum() >= max(1, cnt[order[0]] // 10) or len(batch) < NP:
                batch.append(int(j)); mask &= ~cv
        for out in pool.imap_unordered(decide, [states[j] for j in batch]):
            f.write(json.dumps(out) + '\n'); f.flush()
            s_ = tuple(out['M1'])
            if out['res'] == 'ADV': adv.append(s_)
            else: other[s_] = out['res']
        tried[batch] = True
        Ma = np.array([adv[-1][:7]])  # cheap incremental update below
        newadv = [states[j] for j in batch if states[j] in set(adv)]
        if newadv:
            Mn = np.array([s_[:7] for s_ in newadv])
            cov = np.any(np.all(Mn[:, None, :] + R[None, :, :] <= SV + 1e-6, axis=2), axis=0)
            left[idx[cov]] = False
        P('  %s batch: %d decided (%d ADV); requests left %d / %d; %.0fs' % (tagr, len(batch), len(newadv), left.sum(), len(reqs), time.time() - t0))
    return left


def refute(pool, f, reqs, adv, other, P, t0):
    """tier 1: greedy over his canonical answers; tier 2: all candidates (vol, box) of what is left"""
    reqs = np.array(reqs)
    left = ~covered_mask(adv, reqs)
    if not left.any(): return reqs[left]
    cl = pool.map(canon_only, [tuple(r) for r in reqs[left]], chunksize=8)
    states = sorted({s_ for c in cl for s_ in c})
    P('  tier 1: %d uncovered requests, %d canonical candidate states' % (left.sum(), len(states)))
    left = greedy_round(pool, f, reqs, left, states, adv, other, P, t0, 'tier1')
    if left.any():
        cl = pool.map(cands, [tuple(r) for r in reqs[left]], chunksize=2)
        states = sorted({s_ for c in cl for s_ in c})
        P('  tier 2: %d uncovered requests, %d candidate states (canon+box+vol)' % (left.sum(), len(states)))
        left = greedy_round(pool, f, reqs, left, states, adv, other, P, t0, 'tier2')
    return reqs[left]


if __name__ == '__main__':
    tag = MODE + (os.path.basename(sys.argv[5]).replace('.json', '') if len(sys.argv) > 5 else '')
    logf = open(os.path.join(HERE, 'logs', 'cover2_a%g_d%g_%s.log' % (AL, DE, tag)), 'a')
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); logf.write(s + '\n'); logf.flush()
    adv, other = load(); t0 = time.time()
    P('alpha=%g t=%g mode %s: %d ADV states loaded' % (AL, T, tag, len(adv)))
    with mp.Pool(NP) as pool, open(FN, 'a') as f:
        if MODE == 'grid':
            reqs = grid_requests(float(sys.argv[5]))
            P('grid h=%s: %d maximal first requests; %d already avoided by ADV states'
              % (sys.argv[5], len(reqs), covered_mask(adv, reqs).sum()))
            bad = refute(pool, f, reqs, adv, other, P, t0)
            P('FINAL grid h=%s: unrefuted %d of %d' % (sys.argv[5], len(bad), len(reqs)))
            for r in bad[:40]: P('  UNREFUTED R1', [round(x, 4) for x in r])
        elif MODE == 'list':
            reqs = np.array(json.load(open(sys.argv[5])))
            P('list %s: %d first requests; %d already avoided by ADV states' % (os.path.basename(sys.argv[5]), len(reqs), covered_mask(adv, reqs).sum()))
            bad = refute(pool, f, reqs, adv, other, P, t0)
            P('FINAL list: unrefuted %d of %d' % (len(bad), len(reqs)))
            for r in bad[:40]: P('  UNREFUTED R1', [round(x, 4) for x in r])
        else:
            rounds = int(sys.argv[5]) if len(sys.argv) > 5 else 100
            rng = np.random.default_rng(int(time.time()))
            for rnd in range(rounds):
                adv_p = pareto(adv); P('  %d Pareto-minimal states' % len(adv_p)) if rnd == 0 else None
                e = escaping(adv_p)
                if e is None:
                    P('CONVERGED round %d: no request with |R1| <= t escapes the %d ADV states (%.0fs)' % (rnd, len(adv), time.time() - t0)); break
                if e == 'TIMEOUT': P('escape MILP timeout'); break
                es = [e]
                for j in range(NP - 1):
                    ee = escaping(adv_p, obj=list(rng.normal(size=7)), seed=j)
                    if isinstance(ee, tuple) and all(max(abs(a - b) for a, b in zip(ee, q)) > 1e-3 for q in es): es.append(ee)
                P('round %d: %d escaping R1, e.g. %s' % (rnd, len(es), [round(x, 4) for x in e]))
                bad = []
                known = set(other) | set(adv)
                for r_, outs in zip(es, pool.map(biggest_box, [(e_, known) for e_ in es])):
                    ok = False
                    for out in outs:
                        f.write(json.dumps(out) + '\n'); f.flush(); s_ = tuple(out['M1'])
                        if out['res'] == 'ADV': adv.append(s_); ok = True
                        else: other[s_] = out['res']
                    if not ok: bad.append(r_)
                P('  round %d: %d/%d escaping requests refuted (%.0fs)' % (rnd, len(es) - len(bad), len(es), time.time() - t0))
                bad = np.array(bad)
                if len(bad):
                    P('OPEN: escaping requests with no refuting candidate:'); [P('   ', [round(x, 5) for x in r]) for r in bad]
                    json.dump([list(r) for r in bad], open(os.path.join(HERE, 'logs', 'open_cont_a%g_d%g.json' % (AL, DE)), 'w'))
                    break
