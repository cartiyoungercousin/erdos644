"""Replay of strategy PS (PETAL §26.3) on pooled / asymmetric arena families; exact brute-force 2-cover test.
Usage: py run_ps.py [games]
"""
import sys, os
sys.path.insert(0, os.path.dirname(__file__))
from pool_strip import Fam, tau_profile, search, ps_cost_bound


def choose_X(F, T):
    best = None
    for X in (0, 1):
        b = T - F.tau_c(1 - X)
        if 3 * b < F.k: continue  # running intersection would not empty in four petals
        cb = ps_cost_bound(F, T, X)
        if best is None or cb < best[1]: best = (X, cb)
    return best


def inst(k, T, tA, tF, dA, dF, m, po=False):
    nA, nF = tA - 1 + k - dA, tF - 1 + k - dF
    return (k, T, nA, nF, dA, dF, m, po)


INST = [
    # k, T, tauA, tauF, dA, dF, pool
    inst(40, 32, 17, 16, 2, 2, 12), inst(40, 32, 17, 16, 3, 3, 12), inst(40, 32, 17, 16, 4, 4, 12),
    inst(40, 32, 17, 16, 5, 5, 0), inst(40, 32, 17, 16, 5, 5, 12), inst(40, 32, 17, 16, 5, 5, 40),
    inst(40, 32, 17, 16, 5, 5, 40, True),
    inst(40, 32, 17, 16, 6, 6, 40),                      # delta = 3t/16 (beyond the strip)
    inst(60, 47, 24, 24, 5, 5, 30), inst(60, 47, 24, 24, 6, 6, 30), inst(60, 47, 24, 24, 7, 7, 30, True),
    inst(100, 80, 41, 40, 4, 4, 60), inst(100, 80, 41, 40, 8, 8, 60), inst(100, 80, 41, 40, 13, 13, 60),
    inst(100, 80, 41, 40, 13, 13, 120, True),
    inst(40, 34, 18, 17, 5, 5, 30),                      # t = 0.85
    # asymmetric
    inst(60, 48, 20, 29, 3, 7, 40), inst(60, 48, 26, 23, 9, 4, 40), inst(80, 64, 30, 35, 6, 10, 60, True),
    inst(100, 80, 45, 36, 12, 7, 80),
    # sharpness controls (predicted overrun)
    inst(40, 32, 17, 16, 7, 7, 40), inst(100, 80, 41, 40, 16, 16, 80),
]

if __name__ == "__main__":
    games = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    print("k T | nA nF dA dF m pool_only | t delta_max 3t/16 | tau(H) exact | X bound | games covers viol maxreq centre_max maxcov flags")
    for (k, T, nA, nF, dA, dF, m, po) in INST:
        F = Fam(k, nA, nF, dA, dF, m, pool_only=po)
        tau = tau_profile(F)
        X, cb = choose_X(F, T)
        st = search(F, T, X, games, seed=k * 1000 + dA * 10 + dF + m)
        print("%d %d | %d %d %d %d %d %s | %.3f %.3f %.3f | %d | %d %d | %d %d %d %d %d %d %s" % (
            k, T, nA, nF, dA, dF, m, int(po), T / k, max(dA, dF) / k, 3 * T / (16 * k), tau, X, cb,
            st["games"], st["covers"], st["viol"], st["maxreq"], st["cmax"], st["maxcov"], sorted(st["flags"])), flush=True)
