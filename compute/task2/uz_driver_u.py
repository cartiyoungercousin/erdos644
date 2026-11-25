r"""UNIFORM variant driver (Lemma 4U (ii)).
Driver: run uz_profile.py on every incidence class of every near-pool 2-cell profile family at (k,T,n) = (10,8,21),
cells A (18 points) + Y (3 points = the pool, |Y| = omega), co-edges of size c = 11 with profiles (11-b, b).
T-covering forces (8,3) in P (an 8-set of profile (5,3) lies only in (a,3) co-edges) [proved by hand]; the other
profiles (9,2), (10,1), (11,0) are free, eta = 3 - min b.  Usage: py -3.14 uz_driver.py [workers] [secs]"""
import itertools, json, subprocess, sys, os
from concurrent.futures import ThreadPoolExecutor
HERE = os.path.dirname(os.path.abspath(__file__))
W = int(sys.argv[1]) if len(sys.argv) > 1 else 12; TL = float(sys.argv[2]) if len(sys.argv) > 2 else 1500
jobs = []
for r in range(4):
    for sub in itertools.combinations([(9, 2), (10, 1), (11, 0)], r):
        P = [(8, 3)] + list(sub); eta = 3 - min(b for a, b in P)
        for p in P:
            for side in ('A', 'Y'):
                if (side == 'A' and p[0] >= 18) or (side == 'Y' and p[1] >= 3): continue
                jobs.append({'nA': 18, 'nY': 3, 'T': 8, 'P': P, 'K': p, 'side': side, 'tag': f'eta={eta} P={P}'})
def run(j):
    try:
        r = subprocess.run([sys.executable, os.path.join(HERE, 'uz_profile_u.py'), json.dumps(j)], capture_output=True, text=True, timeout=TL)
        return (r.stdout.strip() or r.stderr.strip()[-300:])
    except subprocess.TimeoutExpired:
        return f"[{j['tag']}] TIMEOUT ({TL}s): K profile {tuple(j['K'])}, z in {j['side']} -- undecided"
with ThreadPoolExecutor(W) as ex:
    for line in ex.map(run, jobs): print(line, flush=True)
