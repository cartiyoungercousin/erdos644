import time
from common import *
from vt import find_cover_vt
n=15; M=sets_of_size(15,8); fk=M[pc(M & 255)%2==1]
K=sets_of_size(14,8); t=time.time(); print(find_cover_vt(K,14,7), time.time()-t,flush=True)
t=time.time(); print(find_cover_vt(fk,15,7), time.time()-t,flush=True)
