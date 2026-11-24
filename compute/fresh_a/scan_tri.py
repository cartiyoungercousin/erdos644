import sys, io, contextlib
from piecewise import sstar, tau
for t in [0.25,0.5,0.75,1.5,2.0]:
    sig=[1,1,t]; pieces=[(0,1),(1,2),(0,2)]
    st,val,asg,sup=sstar(sig,pieces)
    sizes=[val*x for x in sig]
    print("RESULT sig",sig,"s*",round(val,5),"ground",round(sum(sizes),5),"tau",round(tau(sizes,pieces),5),"asg",asg); sys.stdout.flush()
