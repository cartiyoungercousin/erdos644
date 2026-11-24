from fractions import Fraction as Fr
res=set()
for ti in range(66,101):
    t=Fr(ti,100)
    for di in range(0,400):
        d=Fr(di,1000)
        if d>=1-t: break
        n=1+t/2-d
        # worst: S entirely in other arena of chosen colour? check both
        for c in 'AF':
            for x in (t, t/2, Fr(0)):
                # |S ∩ other arena| = x ; |S ∩ own| = t-x  (colour c must be allowed by rule)
                own=t-x; oth=x
                allowed = (c=='F' and oth>t/2) or (c=='A' and own>t/2 and False) 
                # recompute via rule: S∩V_A = A_s, S∩V_F = F_s
                A_s,F_s = (oth,own) if c=='F' else (own,oth)
                col = 'F' if A_s>t/2 else ('A' if F_s>t/2 else c)
                if col!=c: continue
                if n-own<1-d or n-oth<d: res.add((float(t),float(d),c,float(x)))
print(sorted(res)[:20], len(res))
