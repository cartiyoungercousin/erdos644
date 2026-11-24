import spoil as SP, sys
t=0.76
for N in (1.82,1.9,1.96):
    E=SP.Engine(t,N); c=N-1; a=N/2-0.625; o=a+0.005; om=E.om
    m={3:o,1:c-o,2:c-o,0:N-2*c+o}; s={1:a,2:a,0:t-2*a}
    print(N,"base",round(E.base,4),"pair",round(E.min_need(m,2),4), "free g", m[0]-s[0])
    for name,d in (("O",{3:om}),("g",{0:min(om,m[0]-s[0])}),("A",{1:om}),("A/B",{1:om/2,2:om/2}),("O+g",{3:om/2,0:om/2}),("O+g 3/4",{3:.75*om,0:om/4})):
        if abs(sum(d.values())-om)>1e-9: continue
        m2=E.step(m,s,d,4)
        print("   ",name,[ (R,pi,round(E.need_of(m2,R,pi),4)) for R,pi in E.readings(3,new=2)])
