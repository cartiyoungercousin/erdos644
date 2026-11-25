import itertools, time
from toy_complex import report
C = itertools.combinations
# PG(2,3): points 0..12, lines {i, i+1, i+3, i+9} mod 13 (perfect difference set {0,1,3,9})
pg23 = [{(i + d) % 13 for d in (0, 1, 3, 9)} for i in range(13)]
for name, fam in [("K^(4)_5 (A0-tight)", [set(e) for e in C(range(5), 4)]),
                  ("PG(2,3) lines", pg23),
                  ("K^(2)_3 + K^(2)_3 disj", [{0,1},{1,2},{0,2},{3,4},{4,5},{3,5}])]:
    t = time.time(); report(name, fam); print("  secs", round(time.time() - t, 1), flush=True)
