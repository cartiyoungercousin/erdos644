"""How close do the recorded winning responses come to the looseness bound?
For every stuck record: for each response and each pair cell c it avoids (so that c could have
been sealed), S' = |c| + |K & A1| + |K & A2|.  Prints the distribution of 3 - 2t - S'.
usage: py looseness_slack.py out/grid_....jsonl T"""
import sys, json
from fractions import Fraction
import game
fn = sys.argv[1]; t = float(Fraction(sys.argv[2])); pden = int(fn.replace("\\", "/").split("_")[-2])
sl = []; slS = []
for line in open(fn):
    r = json.loads(line)
    if r.get("win") is not None or "cuts" not in r: continue
    i, j, l = r["p"]; mass = game.cell_mass(i / pden, j / pden, l / pden); S = sum(mass[:3])
    for kvf, losing in r["cuts"]:
        kv = kvf[:6] + [1 - sum(kvf[:6])]
        for c in range(3):
            if mass[c] > 1e-9 and kv[c] <= 1e-9:
                a1, a2 = game.TRIPLE_EDGES[c]
                Sp = mass[c] + sum(u * v for u, v in zip(game.edge_trace_coef(a1), kv)) + sum(u * v for u, v in zip(game.edge_trace_coef(a2), kv))
                sl.append(3 - 2 * t - Sp); slS.append(S - Sp)
sl.sort(); slS.sort()
n = len(sl)
q = lambda a, p: a[min(n - 1, int(p * n))]
print(f"{fn}: {n} (response, avoidable cell) pairs; slack 3-2t-S': min {sl[0]:.3f}, 5% {q(sl,.05):.3f}, median {q(sl,.5):.3f}; "
      f"within 0.01 of the bound: {sum(1 for v in sl if v < 0.01)};   S-S': min {slS[0]:.3f}, 5% {q(slS,.05):.3f}, median {q(slS,.5):.3f}, "
      f"pairs with S' > S: {sum(1 for v in slS if v < -1e-9)}")
