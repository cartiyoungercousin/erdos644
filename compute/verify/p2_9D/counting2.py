from math import comb
def ok(k,r,T):
    n=k+r+T; w=k+r
    return comb(n,w) > (1<<(w-1))*comb(n-k,r)
tot=0;bad=[]
for k in range(1,200):
    for T in range(-(-3*k//4),2*k):
        for r in range(0,2*k):
            n=k+r+T
            if 6*n>=11*k: break
            tot+=1
            if not ok(k,r,T): bad.append((k,r,T))
print(tot,len(bad),bad[:10],max([b[0] for b in bad],default=None))
# extended range 11/6<=N<=1.938 at t>=3/4
tot=0;bad=[]
for k in range(40,260,3):
    for T in range(-(-3*k//4),2*k):
        for r in range(0,2*k):
            n=k+r+T
            if 6*n<11*k: continue
            if 10000*n>19380*k: break
            tot+=1
            if not ok(k,r,T): bad.append((k,r,T))
print(tot,len(bad),bad[:10])
