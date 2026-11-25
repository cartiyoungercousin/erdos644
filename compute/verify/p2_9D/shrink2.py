from counting import g
import numpy as np
# threshold omega at t=0.75 (worst) for shrunk requirement g(om,t-2om)>=0 ; also check other t
for t in (0.75,0.8,0.9,1.0):
    lo,hi=1e-6,0.3
    for _ in range(60):
        mid=(lo+hi)/2
        if all(g(o,t-2*o)>=0 for o in np.linspace(1e-5,mid,300) if t-2*o>0): lo=mid
        else: hi=mid
    print("t=%.2f shrunk-ok omega<%.4f  (N=1+om+t=%.4f)"%(t,lo,1+lo+t))
