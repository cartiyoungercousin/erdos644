import time
from common import *; from fano import *; import random
S=sets_of_size(14,8); rng=random.Random(1)
t=time.time(); print(find_fano_fast(S,14,rng), time.time()-t)
t=time.time(); 
for _ in range(20): find_fano_fast(S,14,rng)
print((time.time()-t)/20)
