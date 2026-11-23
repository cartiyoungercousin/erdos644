"""Validate an explicit witness for the symmetric allocation (manuscript Lemmas 3.3-3.4).
Need 0<=a1<=m, 0<=a2<=y, 0<=a3<=z with a2+a3 >= k+m-T, a1+a3 >= k+y-T, a1+a2 >= k+z-T,
a1+a2+a3 <= T, given m>=y>=z, T<=k and the four conditions of Lemma 3.4."""
import itertools
def hyp(k,T,m,y,z):
    S=m+y+z
    return m>=y>=z>=0 and T<=k and m+y<=k and T>=k+m-y-z and 2*T>=k+m and 3*T>=2*k+m+y-z and 5*T>=3*k+S
def wit(k,T,m,y,z):
    L1,L2,L3=k+m-T,k+y-T,k+z-T
    t=min(T,m+y+z)
    u1,u2=min(m,t-L1),min(y,t-L2)
    a1=u1; a2=min(u2,t-a1); a3=t-a1-a2
    return a1,a2,a3
bad=n=0
for k in range(0,40):
  for T in range(0,k+1):
    for m in range(k+1):
      for y in range(m+1):
        for z in range(y+1):
          if hyp(k,T,m,y,z):
            n+=1; a1,a2,a3=wit(k,T,m,y,z)
            ok=0<=a1<=m and 0<=a2<=y and 0<=a3<=z and a2+a3>=k+m-T and a1+a3>=k+y-T and a1+a2>=k+z-T and a1+a2+a3<=T
            if not ok:
              bad+=1
              if bad<5: print(k,T,m,y,z,(a1,a2,a3))
print("cases",n,"failures",bad)
