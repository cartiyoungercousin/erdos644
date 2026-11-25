from common import *
M,n,_=load_family('ref_fkw_m2')
ok,v,cov=is_72_ilp(M,n)
B=[int(M[i]) for i in cov]; print(ok,v,[bin(b) for b in B])
# independent check: do the 7 members have a 2-point transversal?
tr=[(u,w) for u in range(n) for w in range(u+1,n) if all(((b>>u)&1) or ((b>>w)&1) for b in B)]
print('2-transversals of these 7:', tr, 'sizes', [bin(b).count('1') for b in B])
