"""Two blocks, discrete profile sets P = arithmetic progression net (minimal P giving tau > T).
Scan (n1, n2, offset) for target T and report any that the 7-edge MILP adversary cannot break."""
import sys, itertools, time
from profile_milp import bad7, tau
T = float(sys.argv[1]) if len(sys.argv) > 1 else 0.76
good = []
cnt = 0
t0 = time.time()
grid = [round(0.70 + 0.05 * i, 2) for i in range(15)]
for n1 in grid:
    for n2 in grid:
        if n2 < n1: continue
        n = n1 + n2
        s = n - 1 - T
        if s <= 0.01: continue
        if n1 - s > 1 or n2 - s > 1: continue
        for frac in (0.25, 0.5, 0.75, 0.999):
            step = s * 0.999
            top = min(1.0, n1) if n1 - s * (1 - frac) > 1 else n1 - s * (1 - frac)
            P = []
            a = top
            lowlim = max(0.0, 1 - n2)
            while a >= max(lowlim, n1 - T - s) - 1e-9:
                P.append(round(a, 6)); a -= step
            # make sure lowest window is hit
            if not P: continue
            boxes = [([a, 1 - a], [a, 1 - a]) for a in P if 0 <= a <= 1]
            tv, tt = tau([n1, n2], boxes)
            if tv < T - 1e-3: continue
            cnt += 1
            bad, wit = bad7([n1, n2], boxes, enlarge=0.002, tl=60, want_witness=False)
            if bad is not True:
                good.append((n1, n2, frac, P, tv, bad, wit))
                print("NOT BROKEN:", n1, n2, frac, P, "tau", round(tv, 4), bad, wit, flush=True)
print("T", T, "tested", cnt, "unbroken", len(good), "time", round(time.time() - t0, 1))
