r"""Route 3 at small n, exact: random coset families with MANY classes (codimension M close to log2 n or more,
most cells singletons).  Dead points removed (exact DP), k with 0 <= 4n - 7k <= 24, parity-correct disjoint Omegas
with W <= 4n - 7k (greedy exact-min BFS, fam.omegas; so H01 = False is inconclusive).  Ground truth: SAT (task3 sat_check, Fano-type and, if that is
UNSAT, any good seven).  Also records whether B1 succeeds and whether 9' hypotheses hold.
usage: route3_sat.py seed count"""
import sys, os, json, random, time
sys.path.insert(0, os.path.dirname(__file__))
from fam import coset_from_columns
from b1 import b1_construct
from core import Coset, evenise, popc
from fam import omegas
from sat_check import good_seven_sat
from proof_mode import hypotheses

def alive_points(n, cols, alpha, k):
    """x is in some member iff some (k-1)-subset of V - x has column sum alpha ^ cols[x]; exact DP"""
    alive = []
    for x in range(n):
        reach = [set() for _ in range(k)]; reach[0].add(0)
        for y in range(n):
            if y == x: continue
            for j in range(k - 1, 0, -1):
                reach[j] |= {s ^ cols[y] for s in reach[j - 1]}
        if (alpha ^ cols[x]) in reach[k - 1]: alive.append(x)
    return alive

def one(rng):
    n0 = rng.randint(14, 26); M = rng.randint(4, 8)
    cols = [rng.getrandbits(M) for _ in range(n0)]
    alpha = rng.getrandbits(M) or 1
    ks = [k for k in range(2, n0) if 0 <= 4 * n0 - 7 * k <= 24]
    if not ks: return None
    k = rng.choice(ks)
    al = alive_points(n0, cols, alpha, k)
    cols = [cols[x] for x in al]; n = len(cols)
    if n < k or 4 * n - 7 * k < 0: return dict(skip='too few alive')
    cs0 = coset_from_columns(n, cols, M, alpha)
    cs = evenise(cs0, k)
    rec = dict(n=n, k=k, M=M, cells=len(set(cols)), slack=4 * n - 7 * k, cols=cols, alpha=alpha)
    Os = omegas(cs, cs.r)
    W = sum(popc(O) for O in Os) if Os else None
    rec['W'] = W
    if W is None or W > 4 * n - 7 * k: rec['H01'] = False; return rec
    else:
        rec['H01'] = True
        h = hypotheses(cs, k, Os); rec['9prime'] = h.get('all')
        rep = {}; B = b1_construct(cs, k, Os, rng=rng, report=rep)
        rec['B1'] = B is not None; rec['B1fail'] = rep.get('fail')
    t0 = time.time(); st, _ = good_seven_sat(cs, k, mode='fano'); rec['fano'] = st; rec['sat_sec'] = round(time.time() - t0, 1)
    return rec

if __name__ == '__main__':
    seed, count = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    out = open(os.path.join(os.path.dirname(__file__), 'logs', f'route3_s{seed}.jsonl'), 'w')
    done = 0
    while done < count:
        rec = one(rng)
        if rec is None or 'skip' in rec: continue
        done += 1
        out.write(json.dumps(rec) + '\n'); out.flush()
        print(done, rec, flush=True)
