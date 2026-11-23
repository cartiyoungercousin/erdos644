"""Outer loop: optimization of the first request D by constraint generation.

D ranges over the grid  d_c = n_c/den (+ the remainder rho = t - floor(t*den)/den on one cell),
0 <= d_c <= mass_c, sum d = t.  (Profiles are on the same grid, so "cell c sealed" is the grid
event n_c = mass_c*den.)

Loop:  pick a request D not yet answered by a recorded response (all grid requests are kept in
a boolean table) -> inner game play(D) (game.py):
  requester wins D  -> profile is a requester win (certificate: D + pattern pool);
  adversary wins with a response K -> K is shrunk greedily (mass moved to new points while the
     response still wins, so that it stays admissible against more requests) and recorded (the shrinking uses the fast sub-tables; the recorded win patterns of the
     final response are confirmed with the complete tables).
     For every seal pattern s contained in the pair cells that K avoids we record whether K still
     wins when exactly the cells of s are sealed (looseness rows of s + closures of s).  Cut:
        D must intersect K (d_c > mass_c - k_c for some cell c)  or  seal a pattern under which
        K does not win.
  no request left -> for EVERY grid request D one of the recorded responses is admissible and
     wins: the profile is stuck (for this D-grid, modulo floating point).
"""
from __future__ import annotations
import itertools, math
import numpy as np
import pulp
import game
from game import cell_mass, region_mass, EPS, CELL_NAMES


def seal_request(mass, sub):
    """a request vector that seals exactly the pair cells in sub (only its seal pattern matters)."""
    return [mass[c] if (c in sub or mass[c] <= EPS) else 0.0 for c in range(3)] + [0.0, 0.0, 0.0]


def wins_under(mass, kv, sub, t, rules, tol, full=False):
    """does response kv (which avoids the cells of sub) beat the requester when exactly the cells
    of sub (and the empty cells) are sealed?  Capacities are checked separately."""
    d = seal_request(mass, sub)
    if not game.admissible(mass, d, kv, rules, check_cap=False): return False
    v, C, i = game.closure_value(mass, d, kv, stop_at=t + tol)
    if full and v > t + tol:       # confirm a win with the complete pattern tables
        v, C, i = game.closure_value(mass, d, kv, stop_at=t + tol, full=True)
    return v > t + tol


def shrink(mass, d, kv, t, rules, tol, kden=None):
    """greedily move mass of K from known cells to new points while K keeps winning under the
    seal pattern of d."""
    sub = tuple(c for c in range(3) if d[c] >= mass[c] - EPS and mass[c] > EPS)
    kv = list(kv)
    for c in sorted(range(6), key=lambda c: -kv[c]):
        if kv[c] <= 1e-9: continue
        lo, hi = 0.0, kv[c]            # smallest amount in cell c that keeps the win
        trial = kv[:]; trial[6] += trial[c]; trial[c] = 0.0
        if wins_under(mass, trial, sub, t, rules, tol): kv = trial; continue
        if kden:
            n0 = round(kv[c] * kden); a, b = 0, n0        # a loses, b wins
            while b - a > 1:
                mid = (a + b) // 2
                trial = kv[:]; trial[6] += kv[c] - mid / kden; trial[c] = mid / kden
                if wins_under(mass, trial, sub, t, rules, tol): b = mid
                else: a = mid
            trial = kv[:]; trial[6] += kv[c] - b / kden; trial[c] = b / kden; kv = trial
            continue
        for _ in range(4):
            mid = (lo + hi) / 2
            trial = kv[:]; trial[6] += kv[c] - mid; trial[c] = mid
            if wins_under(mass, trial, sub, t, rules, tol): hi = mid
            else: lo = mid
        trial = kv[:]; trial[6] += kv[c] - hi; trial[c] = hi; kv = trial
    return kv


def make_cut(mass, kv, t, rules, tol):
    """minimal seal patterns (subsets of the nonempty pair cells avoided by K) under which K does
    NOT win; None if K wins under no pattern at all (then it is useless)."""
    free = [c for c in range(3) if mass[c] > EPS and kv[c] <= 1e-9]
    losing = []
    win_any = False
    for n in range(len(free) + 1):
        for sub in itertools.combinations(free, n):
            if any(set(m) <= set(sub) for m in losing): continue
            if wins_under(mass, kv, sub, t, rules, tol, full=True): win_any = True
            else: losing.append(sub)
    return losing if win_any else None


class RequestGrid:
    """All grid requests D of one profile, with an 'alive' mask (not yet answered by a recorded
    response).  d_c = n_c/den + (rho if c is the remainder cell), sum = t, d_c <= mass_c."""

    def __init__(self, mass, t, den, seed=0):
        self.mass, self.den = mass, den
        Mc = [int(round(mass[c] * den)) for c in range(6)]
        base = math.floor(t * den + 1e-9); rho = t * den - base
        if rho < 1e-9: rho = 0.0
        self.rho = rho
        grids = np.meshgrid(*[np.arange(Mc[c] + 1, dtype=np.int16) for c in range(5)], indexing="ij")
        n5 = np.stack([g.ravel() for g in grids], axis=1).astype(np.int32)
        last = base - n5.sum(axis=1)
        ok = (last >= 0) & (last <= Mc[5])
        N = np.concatenate([n5[ok], last[ok][:, None]], axis=1)
        if rho:
            parts = []
            for e in range(6):
                sel = N[N[:, e] + 1 <= Mc[e]]
                parts.append(np.concatenate([sel, np.full((len(sel), 1), e, dtype=np.int32)], axis=1))
            NE = np.concatenate(parts, axis=0)
        else:
            NE = np.concatenate([N, np.full((len(N), 1), -1, dtype=np.int32)], axis=1)
        self.N = NE[:, :6]; self.e = NE[:, 6]
        self.seal = np.zeros(len(NE), dtype=np.int8)
        for c in range(3):
            if Mc[c] > 0: self.seal |= ((self.N[:, c] == Mc[c]) & (self.e != c)).astype(np.int8) << c
        self.alive = np.ones(len(NE), dtype=bool)
        self.rng = np.random.default_rng(seed)
        # preference: requests sealing more cells first (they give the requester more options)
        self.nseal = np.array([bin(v).count("1") for v in range(8)])[self.seal]

    def pick(self):
        idx = np.nonzero(self.alive)[0]
        if len(idx) == 0: return None
        best = idx[self.nseal[idx] == self.nseal[idx].max()]
        i = int(self.rng.choice(best))
        d = [self.N[i, c] / self.den + (self.rho / self.den if self.e[i] == c else 0.0) for c in range(6)]
        return [min(v, m) for v, m in zip(d, self.mass)]

    def cut(self, kv, losing):
        """kill every request that is answered by the response kv (which wins under every seal
        pattern contained in its free cells and not containing a set of `losing`)."""
        free = [c for c in range(3) if self.mass[c] > EPS and kv[c] <= 1e-9]
        winpat = np.zeros(8, dtype=bool)
        for n in range(len(free) + 1):
            for sub in itertools.combinations(free, n):
                if not any(set(m) <= set(sub) for m in losing):
                    winpat[sum(1 << c for c in sub)] = True
        fit = winpat[self.seal]
        for c in range(6):
            lim = (self.mass[c] - kv[c]) * self.den + 1e-9
            fit &= (self.N[:, c] + np.where(self.e == c, self.rho, 0.0)) <= lim
        killed = int((fit & self.alive).sum())
        self.alive &= ~fit
        return killed


def solve_profile(x, y, z, t, rules, den=40, tol=1e-6, max_outer=5000, verbose=False, kden=None):
    mass = cell_mass(x, y, z)
    v0, _ = game.phi_static(x, y, z)
    if v0 <= t + tol: return dict(win="static", phi=v0)
    grid = RequestGrid(mass, t, den)
    cuts = []
    for it in range(max_outer):
        d = grid.pick()
        if d is None:
            return dict(win=None, phi=v0, cuts=cuts, outer=it, nreq=len(grid.alive))
        res = game.play(mass, d, t, rules, tol=tol, kden=kden)
        if res["result"] == "R":
            return dict(win="adaptive", phi=v0, D=d, pool=res["pool"], outer=it, iters=res["iters"])
        if res["result"] == "U":
            return dict(win="undecided", phi=v0, D=d, outer=it)
        kv = shrink(mass, d, res["K"], t, rules, tol, kden)
        losing = make_cut(mass, kv, t, rules, tol)      # uses the complete tables
        killed = grid.cut(kv, losing) if losing is not None else 0
        if killed == 0:
            # numerical corner: fall back to the unshrunk response, then give up on this request
            kv = res["K"]; losing = make_cut(mass, kv, t, rules, tol)
            killed = grid.cut(kv, losing) if losing is not None else 0
            if killed == 0: raise RuntimeError(f"response does not answer its own request {d}")
        cuts.append((kv, losing))
        if verbose:
            print(f"  it {it} D={[round(v, 4) for v in d]} K={[round(v, 4) for v in kv]} "
                  f"val={res['value']:.4f} killed={killed} alive={int(grid.alive.sum())}", flush=True)
    return dict(win="undecided", phi=v0, outer=max_outer, cuts=cuts)


if __name__ == "__main__":
    import sys, time
    from fractions import Fraction
    x, y, z, t = (float(Fraction(a)) for a in sys.argv[1:5])
    var = sys.argv[5] if len(sys.argv) > 5 else "loose"
    rules = game.make_rules(var, t, x, y, z)
    t0 = time.time()
    r = solve_profile(x, y, z, t, rules, verbose=True)
    print({k: v for k, v in r.items() if k != "cuts"}, "time", round(time.time() - t0, 1))
