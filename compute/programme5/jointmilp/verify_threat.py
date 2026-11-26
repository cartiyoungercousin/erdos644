r"""Targeted independent check (no MILP) of the certificate of M1' = X u 6.75A u B_eps u 1.248 outside (threat line):
second requests of Lemma-Phi shape X + a of A1 + r0 of A0 + y of Y + B_eps + rO of O1 (+ dead), |R2| = t, random."""
import sys, json, random, jm
sys.argv_orig = list(sys.argv)
sys.argv = [sys.argv[0], "7", "0.002", "0", "0"]
from verify_cert import answer, S, T
random.seed(7)
st = [float(x) for x in (sys.argv_orig[1] if len(sys.argv_orig) > 1 else '6,0,6.75,0.002,0,0,0,1.248').split(',')]
d = [json.loads(l) for l in open('logs/cover_v3_a7_d0.002.jsonl') if json.loads(l)['M1'] == st and json.loads(l)['res'] == 'ADV'][0]
m1 = dict(zip(jm.C7, st[:7])); o1 = st[7]; sz = jm.refined(S, m1, o1); bad = 0; N = 20000
for _ in range(N):
    r2 = {('X', 1): sz[('X', 1)], ('X', 0): sz[('X', 0)], ('B', 1): 0.002}; budget = T - 6.002
    rO = random.choice([0, random.uniform(0, o1)]); r0 = random.choice([0, sz[('A', 0)], random.uniform(0, sz[('A', 0)])])
    rest = budget - rO - r0
    a = random.uniform(0.0, min(6.0, sz[('A', 1)])); y = rest - a
    if not (0 <= y <= 5): continue
    r2[('A', 1)] = a; r2[('A', 0)] = r0; r2[('Y', 0)] = y
    best = max((answer(P, PO, sz, o1, r2, rO) or -1) for P, PO in d['cert'])
    if best <= T + 1e-9: bad += 1; print('FAIL', r2, rO, best)
print('threat-line certificate: %d Lemma-Phi-shaped R2 checked, %d failures' % (N, bad))
