import sys, random, math
from fractions import Fraction as Fr
from common import *
from ap import *
def go(fam,T,games=600,seed=3):
    rnd=random.Random(seed)
    def sc(g):
        adv=Adv(fam,g); out=ap_strategy(fam,T,adv.reply)
        r=out['requests']
        if out.get('flags') or len(out['replies'])!=7: return (99,0)
        return (max(len(x) for x in r[-3:]), 0)
    pop=[]
    for _ in range(60):
        g=rand_genome(rnd); pop.append((sc(g),g))
    pop.sort(key=lambda x:-x[0][0]); pop=pop[:6]
    for it in range(games):
        s,g=rnd.choice(pop); g2=mutate(g,rnd); s2=sc(g2); pop.append((s2,g2)); pop.sort(key=lambda x:-x[0][0]); pop=pop[:6]
    return pop[0][0][0]
cases=[(151,112,56,57),(151,112,57,57),(200,150,75,76),(200,150,70,82),(300,225,112,114),(300,225,150,76),(150,112,56,57)]
for k,T,tx,ty in cases:
    for pool in (0,30):
        fam=make_fam(k,T,tx,ty,pool)
        rho=fam.rho; tau=[tx,ty]
        preds=[]
        for X in (0,1):
            Y=1-X
            valid=(tau[0]>=T/2 and tau[1]>=T/2) or (tau[X]>=T/2 and tau[Y]<T/2)
            if valid: preds.append((max(tau[X]+1,2*rho[Y])+(4*rho[X]-(4*rho[X])//3),X))
        print(k,T,"tau",tx,ty,"rho",rho,"pool",pool,"max step2 request found",go(fam,T),"pred (cost,X) per valid orientation",preds,"T",T); sys.stdout.flush()
