from counting import g
import numpy as np
mn=9;arg=None
for om in np.linspace(1e-4,11/6-1.75,200):
    for t in np.linspace(0.75,11/6-1-om-1e-9,100):
        v=g(om,t-2*om)  # worst case after removing 2*(r+1) points, r'=r
        if v<mn: mn=v;arg=(om,t)
print("min g after worst-case shrink:",mn,arg)
