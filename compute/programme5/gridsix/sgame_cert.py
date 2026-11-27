"""S-game rerun with CERTIFIED closures only.  [computed, grid; closures computed exact + re-checked]
The old S-game (sgame.py, unchanged) plus one extra move: a grid triple (q, y, z) (and every permutation) closes if
it lies in a kgen box whose certificate is INFEASIBLE and re-checked (verify_kgen VERDICT OK), restricted to the
part of the box where that box's first-request type is valid.  Boxes are in units k/14 and were computed at
t = 12 - delta (delta = .03, i.e. t = .855); the script refuses any other t.
usage: py sgame_cert.py G nu t certs.json   (certs.json: [{"tag":..., "R0":..., "box":[qlo,qhi,ylo,yhi,zlo,zhi], "t":...}])"""
import sys, os, json, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'adapt'))
import sgame
G = int(sys.argv[1]); nu = float(sys.argv[2]); t = float(sys.argv[3]); certs = json.load(open(sys.argv[4]))
T3 = sgame.load_static(G); gm = sgame.Game(G, T3)
X, Y, Z = gm.X * 14, gm.Y * 14, gm.Z * 14; e = 1e-9; T14 = 14 * t
mark = np.zeros_like(gm.feas)
for c in certs:
    assert abs(c['t'] - T14) < 1e-6, 'certificate t mismatch'
    qlo, qhi, ylo, yhi, zlo, zhi = c['box']
    inb = (X >= qlo - e) & (X <= qhi + e) & (Y >= ylo - e) & (Y <= yhi + e) & (Z >= zlo - e) & (Z <= zhi + e)
    valid = {'A': X + Y + Z <= T14 + e, 'A_G': X + Y + Z <= T14 + e, 'noZ': X + Y <= T14 + e,
             'partY': X + Z <= T14 + e, 'partYnoZ': X <= T14 + e, 'partX': Y + Z <= T14 + e}[c['R0']]
    mark |= inb & valid & (14 - X - Y >= -e) & (14 - X - Z >= -e) & (14 - Y - Z >= -e)
MARK = gm.sym(mark)
print('certified grid triples (all orientations):', int(MARK.sum()), flush=True)
orig = gm.closes
def closes(S, tt):
    CL, lem, Hv = orig(S, tt)
    return CL | MARK, lem, Hv
gm.closes = closes
adv, S, _ = sgame.solve(G, T3, nu, t, game=gm)
print('t=%.5f  %s  |S*|=%d  S*=%s' % (t, 'ADVERSARY' if adv else 'requester', S.sum(), sgame.compact(S, G)), flush=True)
