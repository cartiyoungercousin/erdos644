r"""Certify and measure every family in fam/.  Usage: py -3.14 analyze.py [name ...]   (default: all not yet in out/results.jsonl)
Per family: (7,2) certified exactly (HiGHS min cover of all pairs by complements >= 8; status optimal), tau by ILP and by an
independent bitset enumeration (n <= 22), then coset fractions for rho >= 1 (EXACT), rho >= 2, rho >= 3 and rho > max(4T-3k,0)
(lower bounds by restriction search) with codim and dual distance of the best coset."""
import sys, os, json, glob, time
from common import *
def analyze(name, budget=60):
    M, n, meta = load_family(name); t0 = time.time(); N = len(M)
    sizes = pc(M); k = int(sizes[0]); assert (sizes == k).all()
    ok72, cover, _c = None, None, None
    ok72, cover, _ = is_72_ilp(M, n, tl=600)
    tau = tau_ilp(M, n); tb = tau_bitset(M, n) if n <= 22 else None
    assert tb is None or tb == tau, (tau, tb)
    T = tau - 1; bnd = max(4 * T - 3 * k, 0)
    ths = sorted(set([1, 2, 3, bnd + 1]))
    cf = coset_fractions(M, n, thetas=ths, budget=budget)
    r = dict(name=name, method=meta.get('method'), n=n, k=k, N=N, tau=tau, tau_bitset=tb, three_k_over_4=3 * k / 4,
             tau_minus_3k4=tau - 3 * k / 4, T=T, four_T_minus_3k=4 * T - 3 * k, is72=ok72, min_cover=cover, cert='HiGHS set-cover optimal' if ok72 is not None else 'ILP timeout (uncertified)',
             frac={str(t): round(v[0], 5) for t, v in cf.items()}, exact1=True,
             best={str(t): v[2] for t, v in cf.items()}, theta_b=bnd + 1, secs=round(time.time() - t0, 1))
    return r
if __name__ == '__main__':
    done = set()
    rf = os.path.join(OUT, 'results.jsonl')
    if os.path.exists(rf): done = {json.loads(l)['name'] for l in open(rf)}
    names = sys.argv[1:] or sorted(os.path.basename(p)[:-4] for p in glob.glob(os.path.join(FAM, '*.npy')))
    for nm in names:
        if nm in done: continue
        r = analyze(nm); print(json.dumps(r), flush=True)
        with open(rf, 'a') as f: f.write(json.dumps(r) + '\n')
