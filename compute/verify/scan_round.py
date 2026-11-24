import sys, math, collections
from tqp_verify import *
kmax=int(sys.argv[1])
fails=collections.defaultdict(list)
tot=0
for k in range(1,kmax+1):
    for T in range(math.ceil(3*k/4), k+4):
        for N in range(k+T, 3*k+3):
            c=N-k; om=c-T
            for Z in range(om,(2*N-3*k)//2+1):
                tot+=1
                if P_exists_integer_plan(k,T,N,Z) is None: fails[(k,T)].append((N,Z))
print(tot)
for key,v in sorted(fails.items()): print(key, len(v), v[:6])
