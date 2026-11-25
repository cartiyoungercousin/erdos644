"""FRONTIER §3: density-only forcing of a Z-pair in the stretch 3t-1/2 < N < 3-t (t >= 5/6).

Units k = 1. c = N-1, omega = N-1-t, Z = [N-2t, 3t-2] (Lemma 90.1 window, nonempty iff N <= 5t-2).
  gamma    : T-covering density exponent, density >= 1/C((N-t)k, omega k)          (CORE 91.1 step 1)
  delta_FW : best Frankl-Wilson exponent for an l-avoiding family, l in Z,
             l < c/2 (co-edge form) or l < N-3/2 (edge form); bound C(n, c-l-1)/C(n,c)  (CORE 97/98.1)
  rho_star : exponent of the star {K : K contains Y}, |Y| = 3t-2 (+0): every pairwise intersection
             is >= |Y| > max Z, so it has NO Z-pair; any density-only theorem must allow it.
Prints the worst case over N for a grid of t, and the sign of gamma - rho_star (density route dead
iff rho_star < gamma somewhere, since then a family denser than the covering guarantee has no Z-pair).
First-order entropies (natural log); polynomial factors ignored [computed float].
"""
import math

def h(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * math.log(x) - (1 - x) * math.log(1 - x)

def quantities(N, t):
    c = N - 1
    om = N - 1 - t
    z0, z1 = N - 2 * t, 3 * t - 2
    gamma = (N - t) * h(om / (N - t))
    lstar = min(z1, max(c / 2, N - 1.5))
    dfw = N * (h(c / N) - h((c - lstar) / N)) if lstar >= z0 else float('nan')
    y = z1
    rho = N * h(c / N) - (N - y) * h((c - y) / (N - y))
    return gamma, dfw, rho, z0, z1

def main():
    print(" t       N-range            worst N   gamma    dFW     rho_star  gamma-dFW  gamma-rho")
    for t in [5/6, 0.835, 0.84, 11/13, 0.85, 6/7, 0.86, 0.865, 0.87, 0.874]:
        lo, hi = 3 * t - 0.5, 3 - t
        best = None
        for i in range(1, 400):
            N = lo + (hi - lo) * i / 400
            g, d, r, z0, z1 = quantities(N, t)
            gap = g - d
            if best is None or gap < best[0]:
                best = (gap, N, g, d, r)
        gap, N, g, d, r = best
        # rho margin: worst (smallest) gamma - rho over the stretch
        rm = min(quantities(lo + (hi - lo) * i / 400, t)[0] - quantities(lo + (hi - lo) * i / 400, t)[2]
                 for i in range(1, 400))
        print(f"{t:.4f}  ({lo:.4f},{hi:.4f})  {N:.4f}  {g:.4f}  {d:.4f}  {r:.4f}   {gap:+.4f}    {rm:+.4f}")
    # limit t -> 7/8: stretch shrinks to N = 17/8
    t = 7/8; N = 17/8
    g, d, r, z0, z1 = quantities(N, t)
    print(f"limit t=7/8, N=17/8: gamma={g:.4f} dFW={d:.4f} rho_star={r:.4f}")

if __name__ == "__main__":
    main()


def star_threshold():
    """Smallest t (grid 1e-4) from which rho_star < gamma at EVERY N of the pair-criterion range
    3t-1/2 < N <= min(5t-2, 3-t): above it no density-only theorem can force a Z-pair anywhere."""
    def dead_everywhere(t):
        lo, hi = 3 * t - 0.5, min(5 * t - 2, 3 - t)
        if hi <= lo:
            return None
        for i in range(1, 200):
            N = lo + (hi - lo) * i / 200
            g, d, r, z0, z1 = quantities(N, t)
            if r >= g:
                return False
        return True
    t = 0.7501
    first = None
    while t < 0.875:
        ok = dead_everywhere(t)
        if ok and first is None:
            first = t
        if not ok:
            first = None
        t += 0.0001
    return first

if __name__ == "__main__":
    print("density route dead on the whole range 3t-1/2 < N <= min(5t-2, 3-t) for all t >=", star_threshold())
