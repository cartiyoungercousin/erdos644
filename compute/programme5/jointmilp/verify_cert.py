r"""Independent check of stage-2 certificates (no MILP).  For each refuted M1 state in logs/cover_<tag>.jsonl, draw
random second requests R2 (|R2| = t, random supports, some cells taken in full) and confirm that some certificate
pattern P, answering R2 by keeping min(P_c, |c| - R2_c) per refined cell and filling with fresh outside points,
is a legal member (mass <= 14, every trace with E, F, G, K, M1 in S*) leaving |U| > t.
usage: py -3.14 verify_cert.py alpha delta nstates nR2 [seed]"""
import sys, os, json, random
import jm

AL, DE, NS, NR = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
random.seed(int(sys.argv[5]) if len(sys.argv) > 5 else 0)
S = jm.sizes(AL); T = 12 - DE
HERE = os.path.dirname(os.path.abspath(__file__))


def answer(P, PO, sz, o1, r2, r2O):
    keep = {k: min(P.get('%s%d' % k, 0.0), max(0.0, sz[k] - r2.get(k, 0.0))) for k in sz}
    kO = min(PO, max(0.0, o1 - r2O))
    if sum(keep.values()) + kO > 14 + 1e-9: return None
    trs = [sum(keep[(c, b)] for c in cs for b in (0, 1)) for cs in jm.MEM.values()]
    trs.append(sum(keep[(c, 1)] for c in jm.C7) + kO)
    if not all(jm.in_spec(v, jm.SPEC, 1e-9) for v in trs): return None
    return jm.U_of(S, {c: sz[(c, 1)] for c in jm.C7}, o1, keep)


def rand_r2(sz, o1):
    keys = [k for k in sz if sz[k] > 1e-9] + (['O'] if o1 > 1e-9 else [])
    cap = {k: (sz[k] if k != 'O' else o1) for k in keys}
    r = {k: 0.0 for k in keys}; budget = T
    random.shuffle(keys)
    for k in keys:
        if budget <= 1e-9: break
        u = random.random()
        amt = cap[k] if u < 0.45 else (0.0 if u < 0.7 else random.uniform(0, cap[k]))
        amt = min(amt, budget); r[k] = amt; budget -= amt
    r2O = r.pop('O', 0.0)
    return r, r2O


if __name__ == '__main__':
    fn = os.path.join(HERE, 'logs', os.environ.get('CERT', 'cover_v3_a%g_d%g.jsonl') % (AL, DE))
    sts = [json.loads(l) for l in open(fn)]
    sts = [d for d in sts if d['res'] == 'ADV']
    random.shuffle(sts); bad = 0; tot = 0
    for d in sts[:NS]:
        m1 = dict(zip(jm.C7, d['M1'][:7])); o1 = d['M1'][7]; sz = jm.refined(S, m1, o1)
        pats = d['cert']
        for _ in range(NR):
            r2, r2O = rand_r2(sz, o1); tot += 1
            best = max((answer(P, PO, sz, o1, r2, r2O) or -1) for P, PO in pats)
            if best <= T + 1e-9:
                bad += 1; print('FAIL state', d['M1'], 'R2', {('%s%d' % k): round(v, 4) for k, v in r2.items() if v}, r2O, best)
    print('checked %d (state, R2) pairs on %d states: %d failures' % (tot, min(NS, len(sts)), bad))
