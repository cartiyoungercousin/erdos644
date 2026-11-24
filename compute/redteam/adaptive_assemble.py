"""§14: assemble the full m = 8 strategy tree at T = 0.76, N = 1.8 and replay ALL 64 leaves exactly at T (margin 0).
Root and node 'U' from adaptive_multi_r6mix.json; subtrees 'UU', 'UO' from greedy_mix_*; subtree 'O' from greedy_r4_O
(its root equals r6mix's root to 1e-16 and is overwritten by it).  Writes logs/adaptive_tree_full_T0.76_N1.8.json."""
import json, itertools, tilt, adaptive_replay as A
from fractions import Fraction as Fr
ld = lambda f: {k: {int(J): v for J, v in r.items()} for k, r in json.load(open(f)).items()}
mix = ld("logs/adaptive_multi_r6mix.json"); tree = {"": mix[""], "U": mix["U"]}
for f, p in [("logs/adaptive_tree_greedy_mix_UU.json", "UU"), ("logs/adaptive_tree_greedy_mix_UO.json", "UO"), ("logs/adaptive_tree_greedy_r4_O.json", "O")]:
    t = ld(f); tree.update({k: r for k, r in t.items() if k.startswith(p)})
assert len(tree) == 63, len(tree)
for k, r in tree.items(): assert sum(r.values()) <= 0.76 + 1e-12
rows = []
for bits in itertools.product("UO", repeat=6):
    b = "".join(bits); reqs = [tree[b[:e]] for e in range(6)]
    zq, d, un = A.replay(0.76, 1.8, b, reqs)                    # budget T, mass(D) - T
    zo = tilt.exact_leaf(0.76, 1.8, b, reqs)[0]                 # §13's convention (threshold T + 0.001), for comparison
    rows.append(dict(bits=b, margin_at_T=float(-zq), exact_rational=str(-zq), drop=d, s13_convention=float(-zo)))
json.dump({k: {str(J): v for J, v in r.items()} for k, r in tree.items()}, open("logs/adaptive_tree_full_T0.76_N1.8.json", "w"))
with open("logs/adaptive_verify_full_T0.76_N1.8.log", "w") as f:
    for r in rows: f.write(json.dumps(r) + "\n")
    s = dict(SUMMARY=True, T=0.76, N=1.8, m=8, nodes=len(tree), leaves=64, won=sum(r["margin_at_T"] > 0 for r in rows),
             worst=min(rows, key=lambda r: r["margin_at_T"]), worst_U=min((r for r in rows if r["bits"][0] == "U"), key=lambda r: r["margin_at_T"])["margin_at_T"],
             worst_O=min((r for r in rows if r["bits"][0] == "O"), key=lambda r: r["margin_at_T"])["margin_at_T"])
    f.write(json.dumps(s) + "\n")
print(json.dumps(s))
