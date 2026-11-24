from common import *
from ap import *
for k,T,tx,ty in [(100,72,36,37),(100,70,35,36),(151,111,55,57)]:
    fam=make_fam(k,T,tx,ty,0)
    st=run_search(fam,ap_strategy,T,150,seed=1)
    print(k,T,tx,ty,fam.rho,"maxreq",st['maxreq'],"viol",st['budget_viol'],"loses",st['loses'])
