r"""Monte Carlo: fraction of random first requests (|R1| = t, uniform on the box-truncated simplex) that NO
ADV state of the verified file avoids.  usage: py -3.14 escape_frac.py alpha delta N"""
import sys, json, numpy as np, jm
AL, DE, N = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
S = jm.sizes(AL); T = 12 - DE; SV = np.array([S[c] for c in jm.C7])
adv = np.array([json.loads(l)['M1'][:7] for l in open('logs/cover_v3_a%g_d%g.jsonl' % (AL, DE)) if '"ADV"' in l[:200]])
rng = np.random.default_rng(0); R = []
while len(R) < N:
    x = rng.dirichlet(np.ones(7), size=4 * N) * T
    R.extend(x[np.all(x <= SV, axis=1)])
R = np.array(R[:N]); cov = np.zeros(N, bool)
for i in range(0, len(adv), 200):
    cov |= np.any(np.all(adv[i:i + 200, None, :] + R[None, :, :] <= SV + 1e-6, axis=2), axis=0)
print('%d ADV states; escaping fraction of %d uniform maximal requests: %.5f' % (len(adv), N, 1 - cov.mean()))
