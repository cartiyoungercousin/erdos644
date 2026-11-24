import sys, itertools
from orders_modes import solve
from orders_milp import NAMES
order = tuple(int(ch) for ch in sys.argv[1].split(","))
D = int(sys.argv[2])
Ecl = lambda j: [(True, h) for h in itertools.product((0, 1, 2), repeat=j)]
keep = {1: [(True, (1,)), (True, (0,)), (False, (1,))], 2: Ecl(2), 3: Ecl(3)}
if len(sys.argv) > 3:   # absence-pattern restriction for deeper steps: only requested/present histories
    keep[2] = [(True, h) for h in itertools.product((0, 1), repeat=2)]
    keep[3] = [(True, h) for h in itertools.product((0, 1), repeat=3)] + [(False, h) for h in itertools.product((0, 1), repeat=3)]
print(" ".join(NAMES[i] for i in order), "pruned D =", D, solve(order, D, keep=keep, tl=1500), flush=True)
