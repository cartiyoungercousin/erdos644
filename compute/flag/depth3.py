"""Level-3 adaptive truncation at the lower window end (CORE §77).
Position after K1,K2: overlap o. She requests S3 (profile on O,A,B,g, mass t); he dumps omega on unrequested
mass; she wins at once if some reading R (a pair or a triple of K1,K2,K3, Fano-labelled) has need_R = 0,
i.e. the 7-|R| future lines all have mass <= t (static finish; <= 8 requests in all).
Usage: py -3.14 depth3.py t N [ngrid]"""
import sys, itertools, numpy as np
from fano import need
t = float(sys.argv[1]); N = float(sys.argv[2]); ng = int(sys.argv[3]) if len(sys.argv) > 3 else 12
c = N - 1; om = N - 1 - t
READ = [({0:0,1:1},), ({0:0,2:1},), ({1:0,2:1},), ({0:0,1:1,2:2},), ({0:0,1:1,2:3},)]
PAIRCT = {'O': {0,1}, 'A': {0}, 'B': {1}, 'g': set()}

def cells3(o, s, d):
    m = {'O': o, 'A': c-o, 'B': c-o, 'g': N-2*c+o}
    out = []
    for k in 'OABg':
        inn = s[k] + d[k]; out.append((inn, frozenset(PAIRCT[k] | {2}))); out.append((m[k]-inn, frozenset(PAIRCT[k])))
    return [x for x in out if x[0] > 1e-12]

def wins(o, s, d):
    cl = cells3(o, s, d)
    for (lab,) in READ:
        keep = set(lab)
        # restrict co-types to kept members
        cc = {}
        for m, ct in cl:
            k = frozenset(ct & keep); cc[k] = cc.get(k, 0) + m
        # relabel kept members to 0..r-1 order is irrelevant: need() uses member indices directly
        v = need([(m, k) for k, m in cc.items()], lab, t)
        if v is not None and v <= 1e-9: return True
    return False

def dump_points(cap, n):
    """vertices + grid of {d >= 0, d <= cap, sum d = om} over the 4 cells"""
    ks = 'OABg'; pts = []
    for comb in itertools.product(range(n+1), repeat=3):
        if sum(comb) > n: continue
        f = list(comb) + [n - sum(comb)]
        d = {k: om * f[i] / n for i, k in enumerate(ks)}
        if all(d[k] <= cap[k] + 1e-12 for k in ks): pts.append(d)
    # greedy vertices (fill cells in every order)
    for perm in itertools.permutations(ks):
        r = om; d = {k: 0.0 for k in ks}
        for k in perm:
            a = min(r, cap[k]); d[k] = a; r -= a
        if r < 1e-12: pts.append(d)
    return pts

def o_wins(o, sgrid=24):
    m = {'O': o, 'A': c-o, 'B': c-o, 'g': N-2*c+o}
    best = None
    for i, j, l in itertools.product(range(sgrid+1), repeat=3):
        s = {'O': m['O']*i/sgrid, 'A': m['A']*j/sgrid, 'B': m['B']*l/sgrid}
        s['g'] = t - s['O'] - s['A'] - s['B']
        if s['g'] < -1e-12 or s['g'] > m['g'] + 1e-12 or j > l: continue
        s['g'] = max(0.0, s['g'])
        cap = {k: m[k] - s[k] for k in 'OABg'}
        if sum(cap.values()) < om - 1e-12: continue
        pts = dump_points(cap, 4)
        if all(wins(o, s, d) for d in pts[-24:]) and all(wins(o, s, d) for d in pts):
            pts2 = dump_points(cap, ng)
            if all(wins(o, s, d) for d in pts2): return s
    return None

if __name__ == '__main__':
    lo = max(0, 2*c - N)
    print(f"t={t} N={N} omega={om:.4f} 4eps={4*(t-.75):.4f}")
    for o in np.linspace(lo + 0.15, c - 0.3, int(sys.argv[4]) if len(sys.argv) > 4 else 9):
        s = o_wins(o)
        print(f"o={o:.4f}", "WIN s3=" + str({k: round(v, 4) for k, v in s.items()}) if s else "no S3 found", flush=True)
