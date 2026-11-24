import sys, itertools, pulp
import orders_tree as ot
from orders_milp import ok, NAMES
order = tuple(int(a) for a in sys.argv[2].split(",")); D = int(sys.argv[1])
# re-solve keeping the problem: monkeypatch solve to expose variables
orig = pulp.LpProblem.solve
keep = {}
def spy(self, *a, **k):
    r = orig(self, *a, **k); keep["p"] = self; return r
pulp.LpProblem.solve = spy
print(ot.solve(order, D))
types = [(isE, st) for isE in (True, False) for st in itertools.product((0, 1, 2), repeat=6)
         if ok(isE, frozenset(order[i] for i in range(6) if st[i]))]
vals = {v.name: v.value() for v in keep["p"].variables()}
print("order", [NAMES[i] for i in order], " status per step: . present, R requested, D dropped")
for lf in itertools.product("EN", repeat=D):
    nm = "".join(lf); print("leaf", nm)
    for i, (isE, st) in enumerate(types):
        x = vals.get(f"x_{nm}_{i}", 0) or 0
        if x > 1e-7: print("   ", "E " if isE else "nE", "".join(".RD"[s] for s in st), round(x, 5))
    print("    y", [round(vals.get(f"y_{nm}_{r}", 0) or 0, 5) for r in range(6)])
