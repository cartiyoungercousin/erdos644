"""PETAL 47: point-level exact replay of the cf_tree.py integer plan at (k,T,d) = (24,18,5).

Input: logs/cf_tree_int_24_18_5.json (written by `DUMP=... py cf_tree.py int 24 18 5`).
Requester (point level, all requests <= T verified):
  centres j = 0,1,2: S_j = G_j + K_j, K_j = 8 disjoint points of R_F, G_j = earlier R_A traces + filler, |G_j| = tau_A.
  petal a (after observing the options o_0..o_{a-1}): Y_a = Tri + union of kappa_j with x[h][j] = 1 (+ sealed leak parts
  sl, none in the solution), padded to tau_F points; W_a = window read off the plan's cell masses of a leaf below h
  (cells split group by group, so windows depend only on o_{<a}).  Observation of a reply: o = j if its leak (points outside
  R_A) meets only kappa_j; else o = 3 (leak meets two or more kappa types, or none).
Adversary: EXACT.  For each of the 4^4 observation sequences the requests are fixed; a SAT instance asks for petal replies
  (any 24-set avoiding the request with >= 19 points in R_A, matching the observation), such that the 7 replies have a
  2-point cover.  UNSAT for all 256 = the plan beats every adversary whose centre traces lie in R_A (several trace
  placements tried); a SAT instance prints the adversary's replies (an obstruction for this plan).
Usage: py cf_tree_replay.py [json] [seeds]
"""
import json, sys, os, random, itertools
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from pysat.solvers import Solver

K, T, D = 24, 18, 5
NA, NF, M = 28, 27, 10
RA = list(range(NA)); RF = list(range(NA, NA + NF)); O = list(range(NA + NF, NA + NF + M)); ALL = RA + RF + O
tA, tF = NA - K + D + 1, NF - K + D + 1
KB = [RF[0:8], RF[8:16], RF[16:24]]; TRI = RF[24:27]


def centres(rnd):
    reqs, reps, z = [], [], []
    for j in range(3):
        G = set().union(*z) if z else set()
        for x in RA:
            if len(G) >= tA: break
            G.add(x)
        S = set(G) | set(KB[j]); assert len(S) <= T
        cand = [x for x in RA if x not in S]
        zj = sorted(rnd.sample(cand, D)) if rnd else cand[:D]
        z.append(set(zj)); reqs.append(S); reps.append((set(RF) - set(KB[j])) | set(zj))
        assert not (reps[-1] & S) and len(reps[-1]) == K
    return reqs, reps, z


class Plan:
    def __init__(s, js, z):
        s.nodes = js['nodes']; s.mu = js['mu']; s.z = z; s.cache = {}

    def lab(s, h):   # point -> frozenset of windows <= len(h), for the node with option history h
        if h in s.cache: return s.cache[h]
        a = len(h)
        prev = s.lab(h[:-1]) if a else {x: frozenset() for x in RA}
        leaf = h + '0' * (4 - a)
        cnt = {}
        for key, v in s.mu[leaf].items():
            Ms, j = key.split('|'); Mp = frozenset(int(c) for c in Ms if int(c) <= a); cnt[(Mp, int(j))] = cnt.get((Mp, int(j)), 0) + v
        grp = {}
        for x in RA:
            j = 0
            for i in range(3):
                if x in s.z[i]: j = i + 1
            grp.setdefault((prev[x], j), []).append(x)
        out = {}
        for (Mpp, j), pts in grp.items():
            c = int(round(cnt.get((Mpp | {a}, j), 0)))
            assert c + int(round(cnt.get((Mpp, j), 0))) == len(pts), (h, Mpp, j, c, len(pts))
            for i, x in enumerate(sorted(pts)):
                out[x] = (Mpp | {a}) if i < c else Mpp
        s.cache[h] = out
        return out

    def request(s, h, leaks):
        a = len(h); nd = s.nodes[h]; lab = s.lab(h)
        W = {x for x in RA if a in lab[x]}
        Y = list(TRI)
        for j in range(3):
            if nd['x'][j]: Y += KB[j]
        for (ap, j) in nd['sl']: Y += [p for p in leaks[ap] if p in KB[j]]
        Y = list(dict.fromkeys(Y))
        mult = {p: sum(p in L for L in leaks) for p in RF}
        for p in sorted(RF, key=lambda p: (-mult[p], p)):
            if len(Y) >= tF: break
            if p not in Y: Y.append(p)
        S = W | set(Y)
        return S, len(W), len(Y)


def obs(E):
    th = {j for j in range(3) if E & set(KB[j])}
    return next(iter(th)) if len(th) == 1 else 3


def sat_check(reqs, reps, opts):
    """exists petal replies E_3..E_6 consistent with opts and a 2-cover?  returns replies or None"""
    pool = IDPool(); cl = []
    e = [[pool.id(('e', a, p)) for p in ALL] for a in range(4)]
    c1 = [pool.id(('c1', p)) for p in ALL]; c2 = [pool.id(('c2', p)) for p in ALL]
    for c in (c1, c2):
        cnf = CardEnc.equals(lits=c, bound=1, vpool=pool, encoding=EncType.seqcounter); cl += cnf.clauses
    for a in range(4):
        S = reqs[3 + a]
        for p in S: cl.append([-e[a][p]])
        cl += CardEnc.equals(lits=e[a], bound=K, vpool=pool, encoding=EncType.seqcounter).clauses
        cl += CardEnc.atleast(lits=[e[a][p] for p in RA], bound=K - D, vpool=pool, encoding=EncType.seqcounter).clauses
        hit = [pool.id(('hit', a, j)) for j in range(3)]
        for j in range(3):
            cl.append([-hit[j]] + [e[a][p] for p in KB[j]])
            for p in KB[j]: cl.append([hit[j], -e[a][p]])
        o = opts[a]
        if o < 3:
            cl.append([hit[o]]); cl += [[-hit[i]] for i in range(3) if i != o]
        else:
            for j in range(3): cl.append([-hit[j]] + [hit[i] for i in range(3) if i != j])
    for i in range(7):
        hs = []
        for p in ALL:
            if i < 3 and p not in reps[i]: continue
            hv = pool.id(('h', i, p)); hs.append(hv)
            if i >= 3: cl.append([-hv, e[i - 3][p]])
            cl.append([-hv, c1[p], c2[p]])
        cl.append(hs)
    with Solver(name='cadical153', bootstrap_with=cl) as sv:
        if not sv.solve(): return None
        m = set(l for l in sv.get_model() if l > 0)
        E = [{p for p in ALL if e[a][p] in m} for a in range(4)]
        cv = ({p for p in ALL if c1[p] in m}, {p for p in ALL if c2[p] in m})
        return E, cv


def run(js, seeds):
    total = 0; bad = []
    for seed in seeds:
        rnd = random.Random(seed) if seed is not None else None
        creqs, creps, z = centres(rnd)
        plan = Plan(js, z); sizes = set()
        for opts in itertools.product(range(4), repeat=4):
            reqs = list(creqs); leaks = []
            ok = True
            for a in range(4):
                S, w, y = plan.request(''.join(map(str, opts[:a])), [])    # sealing bits are all 0 in the plan
                if len(S) > T: ok = False; bad.append(('over T', seed, opts, a, len(S)))
                sizes.add((a, w, y)); reqs.append(S)
            r = sat_check(reqs, creps, opts); total += 1
            if r is not None: bad.append(('2-cover', seed, opts, r))
            elif not ok: pass
        print("seed %s: 256 sequences checked, request (petal, |W|, |Y|) shapes %s" % (seed, sorted(sizes)), flush=True)
    return total, bad


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(__file__), 'logs', 'cf_tree_int_24_18_5.json')
    seeds = [None] + list(range(int(sys.argv[2]))) if len(sys.argv) > 2 else [None, 0, 1]
    js = json.load(open(path))
    assert all(not v['sl'] for v in js['nodes'].values()), "plan uses sealing: extend Plan.request"
    total, bad = run(js, seeds)
    print("checked %d scenarios; failures %d" % (total, len(bad)))
    for b in bad[:5]: print(b)
