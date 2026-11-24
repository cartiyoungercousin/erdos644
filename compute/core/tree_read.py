import json, sys, itertools
sys.path.insert(0, r'C:\Users\USER\lean644\compute\redteam')
import tilt
T=0.76; N=1.8
tree={k:{int(J):v for J,v in r.items()} for k,r in json.load(open(r'C:\Users\USER\lean644\compute\redteam\logs\adaptive_tree_full_T0.76_N1.8.json')).items()}
def nm(J): return ''.join(str(i+1) for i in range(7) if J>>i&1) or '-'
def play(bits, upto=6, verbose=False):
    m={0:N-1,1:1.0}; real={1}; out=[]
    for e in range(1,upto+1):
        b=1<<e; sf=tree[bits[:e-1]]
        s={J:(mj if sf.get(J,0)>=mj-3e-5 else (0 if sf.get(J,0)<3e-5 else sf.get(J,0))) for J,mj in m.items()}
        tot=sum(s.values()); a={J:m[J]-s[J] for J in m}; slack=N-tot-1; lam=1/(N-tot)
        ov={J:0 for J in m}; left=slack
        for J in tilt.ORD[bits[e-1]](sorted(m)):
            x=min(left,a[J]); ov[J]=x; left-=x
        desc=[]
        for J in sorted(m,key=lambda J:(bin(J).count('1'),J)):
            if m[J]<1e-9: continue
            tag='FULL' if s[J]>=m[J]-1e-9 else ('none' if s[J]==0 else 'part')
            desc.append((nm(J),round(m[J],4),round(s[J],4),tag,round(.5*(1-lam)*a[J]+.5*ov[J],4)))
        out.append((e+1,bits[e-1],round(tot,4),desc))
        m2={}
        for J in m:
            o=.5*(1-lam)*a[J]+.5*ov[J]; m2[J]=s[J]+o
            if a[J]>1e-12:
                real.add(J|b)
                if a[J]-o>1e-12: m2[J|b]=a[J]-o
        m=m2
    return m,real,out
def ending(m,real):
    best=None
    for drop in range(7):
        I=127&~(1<<drop)
        Dt={J:mj for J,mj in m.items() if any((K&(I&~J))==(I&~J) for K in real)}
        D=sum(Dt.values())
        if best is None or D<best[0]: best=(D,drop+1,Dt,I)
    return best
if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='leaf':
        bits=sys.argv[2]; m,real,out=play(bits)
        for r in out:
            print('reply',r[0],'bit',r[1],'req mass',r[2])
            for d in r[3]: print('    type %-7s mass %.4f req %.4f %s omitted-unreq %.4f'%d)
        D,drop,Dt,I=ending(m,real)
        print('drop',drop,'D',round(D,4))
        # project on kept
        proj={}
        for J,mj in m.items(): proj[J&I]=proj.get(J&I,0)+mj
        for J in sorted(proj,key=lambda J:(bin(J).count('1'),J)):
            if proj[J]>1e-6: print('   kept-type %-7s %.4f %s'%(nm(J),proj[J],'D' if any((K&(I&~J))==(I&~J) for K in real) else ''))
    if mode=='nodes':
        for k in sorted(tree,key=lambda k:(len(k),k)):
            m,real,out=play(k+'U',len(k)+1) if len(k)<6 else None
            r=out[-1]
            print(repr(k),'-> request for reply',r[0],'mass',r[2],' | '.join('%s:%.3f/%.3f%s'%(d[0],d[2],d[1],{'FULL':'*','none':'','part':'~'}[d[3]]) for d in r[3] if d[1]>2e-3))
