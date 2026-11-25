r"""CORE 55.5 cross-check: minimum number of members of a family (file: one member per line) covering all pairs, by MILP (HiGHS).
Usage: py cover_ilp.py famfile n [time_limit]"""
import sys, itertools, highspy, numpy as np
fam = [frozenset(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]; n = int(sys.argv[2])
tl = float(sys.argv[3]) if len(sys.argv) > 3 else 3600
h = highspy.Highs(); h.setOptionValue("time_limit", tl); h.setOptionValue("threads", 8)
m = len(fam)
for i in range(m): h.addVar(0, 1)
h.changeColsIntegrality(m, np.arange(m, dtype=np.int32), np.array([highspy.HighsVarType.kInteger] * m))
h.changeColsCost(m, np.arange(m, dtype=np.int32), np.ones(m))
for x, y in itertools.combinations(range(n), 2):
    idx = [i for i, K in enumerate(fam) if x in K and y in K]
    h.addRow(1, highspy.kHighsInf, len(idx), np.array(idx, dtype=np.int32), np.ones(len(idx)))
c = len(next(iter(fam))); r = -(-(n - 1) // (c - 1))
for x in range(n):
    idx = [i for i, K in enumerate(fam) if x in K]
    h.addRow(r, highspy.kHighsInf, len(idx), np.array(idx, dtype=np.int32), np.ones(len(idx)))
h.run()
info = h.getInfo(); st = h.modelStatusToString(h.getModelStatus())
print(f"{sys.argv[1]}: {m} members; status {st}; best cover {info.objective_function_value}; dual bound {info.mip_dual_bound}")
