import itertools, tree_read as an, collections
rows=[]
for bits in itertools.product("UO",repeat=6):
    b=''.join(bits); m,real,out=an.play(b); D,drop,Dt,I=an.ending(m,real)
    # state after reply 3
    m3,_,_=an.play(b,2)
    kap=m3.get(0,0)
    big=sorted(((an.nm(J&I),) for J in m), key=lambda x:x)
    proj=collections.defaultdict(float)
    for J,mj in m.items(): proj[J&I]+=mj
    bigc=' '.join('%s:%.3f%s'%(an.nm(J),v,'D' if any(((K&(I&~J))==(I&~J)) for K in real) else '') for J,v in sorted(proj.items(),key=lambda kv:(bin(kv[0]).count('1'),kv[0])) if v>0.03)
    rows.append((b,drop,round(0.76-D,4),round(kap,4),bigc))
for r in rows: print(*r)
print(collections.Counter(r[1] for r in rows))
