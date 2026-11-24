import random, ps_check as P
from ps_check import *
rng=random.Random(5)
k,T=60,45
dX=dY=8
hs=feasible_hits(k,T,dX,dY)
found=0
for var,m in (('pool',30),('exact',63),('free',0)):
  fam=mkfam(k,T,0,hs[0],dX,dY,m,var)
  for trial in range(300):
    g,c=rand_genome(rng,rng.randrange(3))
    r=random.Random(trial)
    adv=Adv(fam,g,c,1.0,r)
    # replicate play but expose sets
    sets=[]
    orig=adv.reply
    def rep(S,replies,requests,i,orig=orig):
        out=orig(S,replies,requests,i); 
        if out: sets.append(out[0])
        return out
    adv.reply=rep
    res=play(fam,T,0,adv,r,'low')
    if any(f.startswith('DUP') for f in res['flags']):
        idx={}
        for i,R in enumerate(sets): idx.setdefault(R,[]).append(i+1)
        print(var,trial,[v for v in idx.values() if len(v)>1],res['reqs'][:7]); found+=1
        if found>4: raise SystemExit
