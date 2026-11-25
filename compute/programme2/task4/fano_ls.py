r"""Stronger search for a Fano-type good seven than random balanced colourings: simulated annealing over colourings
chi: V -> {0..6} (NOT necessarily balanced) minimising the number of lines l with no member inside R_l = V \ chi^{-1}(l).
Cost 0 = Lemma 2 applies = a Fano-type good seven exists (exact certificate).  Failure proves nothing.
Usage: py -3.14 fano_ls.py case [restarts] [steps]   case in: core9 | sel17r2 | sel17r3 | fkw16 | tgw15"""
import sys, os, random, math, json
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, '..', 'task1'))
sys.path.insert(0, os.path.abspath(os.path.join(HERE, '..', '..', 'core9')))
import families as F
from measure import FANO
def cost(M, chi, n):
    cls = [0] * 7
    for v, c in enumerate(chi): cls[c] |= 1 << v
    bad = 0
    for l in FANO:
        L = cls[l[0]] | cls[l[1]] | cls[l[2]]
        if not ((M & L) == 0).any(): bad += 1
    return bad
def anneal(M, n, restarts, steps, seed=1):
    rng = random.Random(seed); best = 7
    for r in range(restarts):
        chi = [rng.randrange(7) for _ in range(n)]; c = cost(M, chi, n); T0 = 0.6
        for s in range(steps):
            v = rng.randrange(n); old = chi[v]; chi[v] = rng.randrange(7)
            if chi[v] == old: continue
            c2 = cost(M, chi, n); T = T0 * (1 - s / steps) + 0.02
            if c2 <= c or rng.random() < math.exp((c - c2) / T): c = c2
            else: chi[v] = old
            best = min(best, c)
            if c == 0: return 0, chi, r
    return best, None, restarts
def build_case(case):
    C = F.ROOT
    if case == 'core9': return F.coedge_text(os.path.join(C, 'core9/logs/fam_8_6_15_rev.txt'), 15, 'core9')[0]
    if case == 'tgw15': return F.coedge_masks(os.path.join(C, 'core12/logs/tgw_fam_8_6_15.txt'), 15, 'tgw15')[0]
    if case == 'fkw16':
        from run import fkw_general; return fkw_general(2, 16)
    if case == 'h1': return F.h1()[0]
    if case == 'gprime': return F.npy(os.path.join(C, 'task3/out/gprime_fkw1.npy'), 'gprime')[0]
    if case == 'fkw3': return F.fkw(3)[0]
    import decide_family as D
    from tau_star import Family
    k, T, n, R, mode, seed = {'sel17r2': (8, 6, 17, 2, 'rev', 0), 'sel17r3': (8, 6, 17, 3, 'rand', 1), 'sel15r3': (8, 6, 15, 3, 'rand', 1)}[case]
    fam, sel, orders = D.build(k, T, n, R, mode, seed); full = (1 << n) - 1
    return Family(n, [full ^ K for K in fam], case)
if __name__ == '__main__':
    case = sys.argv[1]; restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 200; steps = int(sys.argv[3]) if len(sys.argv) > 3 else 400
    fam = build_case(case); b, chi, r = anneal(fam.masks, fam.n, restarts, steps)
    out = dict(case=case, n=fam.n, members=len(fam.masks), best_cost=b, found=bool(chi is not None), restarts_used=r, steps=steps, chi=chi)
    print(json.dumps(out), flush=True); open(os.path.join(HERE, 'out', 'fano_ls.jsonl'), 'a').write(json.dumps(out) + '\n')
