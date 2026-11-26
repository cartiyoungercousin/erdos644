"""Route B quick test: after Theorem P's K (class A first request), drop one of E,F,G and keep K.
The new triples are (F,G,K) = (Z=0+, B=beta, A=alpha), (E,G,K) = (Y, 0, alpha), (E,F,K) = (X, 0, beta)
(E cap K is empty; the S-game tables treat 0 as 0+, which is conservative for her).  If the S-game closure table
(static / one adaptive request / heavy route, all with spectrum S*) closes such a triple, she wins in route B.
For every legal Theorem-P K (alpha + beta = 14/14 units, traces in S*) report whether each triple closes.
usage: py -3.14 routeB_triples.py G t     (run from this directory; paths are relative)"""
import sys, os
sys.path.insert(0, os.path.join('..', 'adapt'))
import numpy as np, sgame
G, t = int(sys.argv[1]), float(sys.argv[2])
T3 = sgame.load_static(G); gm = sgame.Game(G, T3)
adv, S, (CL, lem, Hv) = sgame.solve(G, T3, 1000, t, game=gm)
print('G=%d t=%.5f: %s, S* = %s' % (G, t, 'ADVERSARY' if adv else 'REQUESTER', sgame.compact(S, G)), flush=True)
xi, yi = round(6 * G / 14), round(5 * G / 14)
print('critical triple (X,Y,Z)=(%d,%d,0)/%d closes: %s' % (xi, yi, G, bool(CL[xi, yi, 0])), flush=True)
nclose = 0; ntot = 0
for ai in range(G + 1):
    bi = G - ai
    if not (S[ai] and S[bi]): continue
    a, b = ai / G, bi / G
    if not (a > t - 6 / 14 and b > t - 5 / 14 and a >= 6 / 14 and b >= 5 / 14 and b <= 8 / 14 + 1e-9): continue
    ntot += 1
    r = {'FGK': bool(CL[0, bi, ai]), 'EGK': bool(CL[yi, 0, ai]), 'EFK': bool(CL[xi, 0, bi])}
    nclose += any(r.values())
    print('  alpha=%d/%d beta=%d/%d: %s' % (ai, G, bi, G, r), flush=True)
print('legal Theorem-P K: %d; with some closing drop-triple: %d' % (ntot, nclose))
