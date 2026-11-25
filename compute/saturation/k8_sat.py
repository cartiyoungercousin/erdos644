r"""SATURATION Task 1(b): incidences of the core9 pencil-free two-class family at (k,T,n) = (8,6,15).
Family file: compute/core9/logs/fam_8_6_15_rev.txt, one co-edge (7-set of 0..14) per line; edges are complements (8-sets).
An incidence (z, B) with B = V - K, z in B, is SATURATED iff the 8-set S = K + {z} together with at most six members of
the family covers every pair {u,v} of V (u = v allowed) -- i.e. B - {z} and six edges have no 2-point transversal.
(Lemma 2.3 of FABLE_C: S, K_2..K_7 cover all pairs iff U(K_2..K_7) is inside S.) Only pairs not inside S need covering.
All incidences with the same S share the answer.
SAT: one var per member not inside S, sequential-counter "at most six", one clause per pair not inside S; CaDiCaL 1.5.3.
SAT answers are re-checked by plain code (certificate = the six members, written to the jsonl). UNSAT is solver-only.
Each 8-set is decided in a child process with a wall-clock limit; a timeout is recorded as 'undecided'.
Usage: py -3.14 k8_sat.py drive [limit (0 = all)] [seconds per 8-set] [workers] [start; negative = random sample with seed -start]
       py -3.14 k8_sat.py one <index>"""
import sys, json, time, subprocess, os
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
fam = [frozenset(map(int, l.split())) for l in open(os.path.join(HERE, '../core9/logs/fam_8_6_15_rev.txt')) if l.strip()]
n = 15; V = range(n)
assert len(fam) == 2352 and all(len(K) == 7 for K in fam)
famset = set(fam)
S_all = {}
for K in fam:
    for z in V:
        if z not in K: S_all.setdefault(K | {z}, []).append((z, K))
S_list = sorted(S_all, key=sorted)
pairs = [(u, v) for u in V for v in V if u <= v]
def decide(S):
    from pysat.solvers import Cadical153
    from pysat.card import CardEnc, EncType
    cand = [K for K in fam if not K <= S]
    cl = [[i + 1 for i, K in enumerate(cand) if u in K and v in K] for (u, v) in pairs if not (u in S and v in S)]
    card = CardEnc.atmost(lits=list(range(1, len(cand) + 1)), bound=6, top_id=len(cand), encoding=EncType.seqcounter)
    with Cadical153(bootstrap_with=cl + card.clauses) as s:
        if not s.solve(): return None
        m = set(l for l in s.get_model() if l > 0)
    six = [cand[i] for i in range(len(cand)) if i + 1 in m]
    assert len(six) <= 6 and all(K in famset for K in six)
    assert all(any(u in A and v in A for A in [S] + six) for (u, v) in pairs)
    return [sorted(K) for K in six]
if __name__ == '__main__' and sys.argv[1] == 'one':
    print(json.dumps(decide(S_list[int(sys.argv[2])]))); sys.exit()
limit = int(sys.argv[2]) if len(sys.argv) > 2 and int(sys.argv[2]) > 0 else len(S_list)
TL = float(sys.argv[3]) if len(sys.argv) > 3 else 20.0
W = int(sys.argv[4]) if len(sys.argv) > 4 else 16
start = int(sys.argv[5]) if len(sys.argv) > 5 else 0
idxs = list(range(start, min(len(S_list), start + limit)))
if start < 0:  # random sample of `limit` 8-sets, seed = -start
    import random; idxs = sorted(random.Random(-start).sample(range(len(S_list)), limit))
print(f"members {len(fam)}, incidences {sum(len(v) for v in S_all.values())}, distinct 8-sets S {len(S_list)}; "
      f"deciding {len(idxs)} from {start} with {TL}s each, {W} workers", flush=True)
def job(i):
    t = time.time()
    try:
        r = subprocess.run([sys.executable, __file__, 'one', str(i)], capture_output=True, text=True, timeout=TL)
        six = json.loads(r.stdout.strip().splitlines()[-1]); st = 'UNSAT' if six is None else 'SAT'
    except subprocess.TimeoutExpired:
        six, st = None, 'undecided'
    if st == 'SAT':  # independent re-check in the driver
        seven = [set(S_list[i])] + [set(K) for K in six]
        assert len(six) <= 6 and all(frozenset(K) in famset for K in six)
        assert all(any(u in A and v in A for A in seven) for (u, v) in pairs)
    return i, st, six, time.time() - t
cnt = {'SAT': 0, 'UNSAT': 0, 'undecided': 0}; inc = dict(cnt); t0 = time.time()
with open(os.path.join(HERE, f'logs/k8_sat_certs_{start}.jsonl'), 'w') as out, ThreadPoolExecutor(W) as ex:
    for done, (i, st, six, dt) in enumerate(ex.map(job, idxs), 1):
        cnt[st] += 1; inc[st] += len(S_all[S_list[i]])
        out.write(json.dumps({'idx': i, 'S': sorted(S_list[i]), 'status': st, 'secs': round(dt, 2),
                              'incidences': [[z, sorted(K)] for z, K in S_all[S_list[i]]], 'six': six}) + '\n'); out.flush()
        if done % 100 == 0: print(f"  {done}/{len(idxs)} 8-sets {cnt} incidences {inc} ({time.time()-t0:.0f}s)", flush=True)
print(f"DONE 8-sets {cnt}; incidences {inc}; time {time.time()-t0:.0f}s")
