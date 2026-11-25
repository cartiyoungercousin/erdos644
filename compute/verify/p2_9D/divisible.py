from thmD import run
import itertools
out=[]
for m,n in ((3,8),(4,16)):
    cols=[(1<<m)|x for x in range(1<<m)]
    for s in range(1,1<<(m+1)):
        for k in range(2,n):
            r=run(cols,s,k)
            if not r: continue
            ins=r['e']<=min(r['w'],r['T']) and n>=2*r['e']+1
            bound=r['r'] if r['w']%2==0 else r['r']+1
            out.append((m,s,k,ins,r['rho']-bound))
bad=[o for o in out if o[3] and o[4]>0]
print("RM-type (1,x) columns: instances",len(out),"inside hyp",sum(o[3] for o in out),"violations",len(bad))
print("max rho-bound outside:",max(o[4] for o in out if not o[3]) if any(not o[3] for o in out) else None)
