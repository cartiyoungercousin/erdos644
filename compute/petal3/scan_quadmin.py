"""scan of quadmin over leaks (logs/quadmin_scan.log).  usage: py scan_quadmin.py"""
from quadmin import quadmin
for t in [0.75, 0.76, 0.78]:
    for d in [0.01,0.02,0.025,0.03,0.035,0.04,0.05,0.06,0.08,0.1,0.125,0.15,0.2,0.25,0.3]:
        st, v, c = quadmin(t, d)
        print(t, d, st, round(v,5), "R" if v <= t+1e-9 else "A", c, flush=True)
