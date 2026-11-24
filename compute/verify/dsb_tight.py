import sys, random
from common import *
from ds import *
k,T=80,60
def go(d,n,games=400):
    fam=Family(k,n,n,[d,d]); rnd=random.Random(5)
    worst=0
    cur=[rand_genome(rnd) for _ in range(30)]
    def sc(g):
        adv=Adv(fam,g); out=dsb_strategy(fam,T,adv.reply)
        r=out['requests']; 
        return max(len(x) for x in r[-3:]) if len(r)>=3 and len(out['replies'])==7 else 0
    scored=sorted([(sc(g),i,g) for i,g in enumerate(cur)],key=lambda x:-x[0])
    for it in range(games):
        s,_,g=rnd.choice(scored[:5]); g2=mutate(g,rnd); s2=sc(g2); scored.append((s2,it+100,g2)); scored.sort(key=lambda x:-x[0]); scored=scored[:8]
    return scored[0][0]
for d,n in [(5,105),(4,106),(4,109),(4,112),(3,107),(3,115),(3,119),(2,118),(2,128),(1,130)]:
    a0=2*(k-d)-n
    print("d",d,"n",n,"max step2 request",go(d,n),"predicted bound",(n-k+2*d+1)+5*d,"T",T)
