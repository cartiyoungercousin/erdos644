"""power check: drop one point from a tight request of Thm T; the same adversary search should then often win."""
import random, math
from tqp_verify import *
rnd=random.Random(5); found=tot=0
for k in range(3,8):
  for T in range(math.ceil(3*k/4),k+1):
    for N in range(k+T,2*k+3):
      c=N-k
      for (a,b,d,e1,e2,e3,g,kap) in T_instances(k,T,N)[:40]:
        if kap: continue
        K1,K2,K3,cell=build_T(a,b,d,e1,e2,e3,g,kap,k,N)
        S4=set(cell['a']+cell['e3']+cell['g']); S5=set(cell['b']+cell['e2']+cell['g']); S6=set(cell['d']+cell['e1']+cell['g']); S7=set(cell['e1']+cell['e2']+cell['e3'])
        Ss=[S4,S5,S6,S7]
        i=rnd.randrange(4)
        if not Ss[i]: continue
        Ss[i]=set(list(Ss[i])[1:])
        tot+=1
        # adversary may now (at best) also be forced to add; hill-climb many iterations
        n,_=hill([K1,K2,K3],Ss,c,N,rnd,iters=400)
        found+= n>0
print("dropped-point controls:",tot,"beaten:",found)
