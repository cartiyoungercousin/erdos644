import time,sys
from common import *
from pc72 import find_cover_dfs
M,n,meta=load_family('td_complete0.0_n14_k8_T6_s1')
t=time.time(); print('ilp', is_72_ilp(M,n,tl=100), time.time()-t, flush=True)
t=time.time(); print('dfs', find_cover_dfs(M,n,7,limit=300_000_000), time.time()-t, flush=True)
