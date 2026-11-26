"""Depth-2 drop-one frames after (K, M1)  [her side heuristic; every adversary refutation is exact].
After M1 she requests R2 -> M2 and then closes if
  (E)  the E-frame {E,F,G,K,M1,M2} has endpoint mass |U| <= t (final R3 = U), or
  (D)  some 5-member drop-one frame {three of E,F,G,K} + {M1, M2}, or {E,F,G,K,M2}, has a static 2-request cover
       of size <= t (exact cell MILP, SCIP).
His M2 must avoid R2, have mass 14 and meet E, F, G, K, M1 in S*.  An M2 with |U| > t and every static-2 value
> t refutes R2 exactly.  Her R2 candidates: the requests of optimal static-3 covers of every drop frame after M1,
plus random maximal requests.  His candidates: jm.oracle2 (max |U|), robust variants, weighted min-drop answers."""
import sys, os, random, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'jointmilp'))
import numpy as np
import jm
from frames import base_sizes, refine, alive, endpoints, ZEPS
from cover import min_t, requests

S = jm.sizes(7.0); C7 = jm.C7; SPEC = jm.SPEC
FR3 = {'FGKM1': ['F', 'G', 'K', 'M1'], 'EGKM1': ['E', 'G', 'K', 'M1'], 'EFKM1': ['E', 'F', 'K', 'M1'], 'EFGM1': ['E', 'F', 'G', 'M1']}
FR2 = {'FGKM12': ['F', 'G', 'K', 'M1', 'M2'], 'EGKM12': ['E', 'G', 'K', 'M1', 'M2'], 'EFKM12': ['E', 'F', 'K', 'M1', 'M2'],
       'EFGM12': ['E', 'F', 'G', 'M1', 'M2'], 'EFGKM2': ['E', 'F', 'G', 'K', 'M2']}


def atoms1(m1):
    mm = dict(m1); mm['Z'] = ZEPS / 2
    return refine(base_sizes(7.0), [{(c,): v for c, v in mm.items()}])


def atoms2(m1, m2):
    mm = dict(m1); mm['Z'] = ZEPS / 2
    m2z = dict(m2); m2z[('Z', 0)] = ZEPS / 4; m2z[('Z', 1)] = ZEPS / 4
    return refine(base_sizes(7.0), [{(c,): v for c, v in mm.items()}, m2z])


def static_frames(at, frames, r, stop=None):
    sz = {a: s for a, s in at.items() if s > 1e-9}; out = {}
    for nm, fr in frames.items():
        tt, pl = min_t(sz, alive(at, fr), r, tl=60)
        out[nm] = (tt, pl)
        if stop is not None and (tt is None or tt <= stop): break
    return out


def her_R2(m1, o1, t, rng, nrand=20):
    """candidate R2 dicts {(cell,b): amount} (+ r2O = 0)"""
    at = atoms1(m1); out = []
    for nm, (tt, pl) in static_frames(at, FR3, 3).items():
        if pl is None: continue
        for q in requests(pl, 3):
            r2 = {a[:2] if len(a) == 2 else a: v for a, v in q.items() if a[0] != 'Z'}
            tot = sum(r2.values())
            if tot > t: r2 = {a: v * t / tot for a, v in r2.items()}
            out.append((nm, r2))
    keys = [(c, b) for c in C7 for b in (0, 1)]
    sz = {(c, 1): m1[c] for c in C7}; sz.update({(c, 0): S[c] - m1[c] for c in C7})
    for _ in range(nrand):
        order = keys[:]; rng.shuffle(order); left = t; r2 = {}
        for kk in order:
            if left <= 1e-9: break
            v = min(sz[kk], left) if rng.random() < 0.5 else min(sz[kk], left, round(rng.uniform(0, sz[kk]) * 4) / 4)
            if v > 0: r2[kk] = v; left -= v
        out.append(('rand', r2))
    return out


def his_M2(m1, o1, r2, t, rng, nmin=6):
    """candidate legal M2 answers to r2: list of (m2 dict, w)"""
    out = []
    o = jm.oracle2(S, m1, o1, r2, 0.0, t, SPEC)
    if o is not None: out.append((o[1], o[2]))
    for nd in (0.001, 0.5, 3.0):
        o = jm.oracle2_robust(S, m1, o1, r2, 0.0, t, SPEC, need=nd)
        if o is not None: out.append((o[1], o[2]))
    sz = jm.refined(S, m1, o1)
    for j in range(nmin):
        m = jm.Model(); mm = {kk: m.v(0, max(0.0, sz[kk] - r2.get(kk, 0.0))) for kk in sz}
        w = m.v(0, o1); o0 = m.v(0, 14)
        m.row(jm.ex(*[(1, e) for e in mm.values()], (1, w), (1, o0)), 14, 14)
        trs = [jm.ex(*[(1, mm[(c, b)]) for c in cs for b in (0, 1)]) for cs in jm.MEM.values()]
        trs.append(jm.ex(*[(1, mm[(c, 1)]) for c in C7], (1, w)))
        for T_ in trs: jm.interval(m, T_, SPEC)
        wt = {kk: -(rng.uniform(0.5, 1.5) if kk[0] in jm.L else rng.uniform(-0.2, 1.0)) for kk in sz}
        res = m.solve(jm.ex(*[(wt[kk], mm[kk]) for kk in sz], (rng.uniform(-0.2, 0.5), w)), 30)
        if res.status == 0:
            x = res.x
            out.append(({kk: max(0.0, jm.val(x, e)) for kk, e in mm.items()}, max(0.0, jm.val(x, w))))
    return out


def evaluate(m1, o1, m2, w, t):
    """(|U| E-frame, {frame: static-2 value}) for an explicit M2 (stops at the first closing frame)"""
    U = jm.U_of(S, m1, o1, m2)
    if U <= t + 1e-6: return U, {}
    at = atoms2(m1, m2)
    vals = {nm: v[0] for nm, v in static_frames(at, FR2, 2, stop=t + 1e-6).items()}
    return U, vals


def refutes(U, vals, t):
    return U > t + 1e-6 and len(vals) == len(FR2) and all(v is not None and v > t + 1e-6 for v in vals.values())
