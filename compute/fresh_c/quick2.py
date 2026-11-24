"""Two symmetric blocks of size h (n = 2h < 2 so any two edges meet), two interval types
type1: a1 in [al, be], type2: a2 in [al, be].  tau = min(2(h-al), 2h-1) when be = h-ish."""
import sys, time
from profile_milp import bad7, tau
for h, al in [(0.9, 0.52), (0.95, 0.55), (0.95, 0.57), (0.98, 0.57), (0.98, 0.60), (0.99, 0.6)]:
    be = min(1.0, h)
    boxes = [([al, 0], [be, 1 - al]), ([0, al], [1 - al, be])]
    tv, tt = tau([h, h], boxes)
    t0 = time.time()
    bad, wit = bad7([h, h], boxes, tl=100)
    print(f"h={h} al={al} tau={tv:.3f} bad={bad} {time.time()-t0:.1f}s", flush=True)
    if bad:
        print("  types", wit["types"], "profiles", [[round(x, 3) for x in p] for p in wit["profiles"]], flush=True)
