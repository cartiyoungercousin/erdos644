"""Literal Prop 9 counterexample (|X|=|Y|=5, z1,z2, k=5): a+C = {S: |S∩X|,|S∩Y| both odd}."""
import itertools
X=range(0,5);Y=range(5,10);z=[10,11];n=12;k=5
mem=[S for S in itertools.combinations(range(n),k) if sum(i in X for i in S)%2==1 and sum(i in Y for i in S)%2==1]
print("members",len(mem),"every member hits {z1,z2}:",all(10 in S or 11 in S for S in mem),"covered V:",set().union(*map(set,mem))==set(range(n)))
Om=[(0,5),(1,6),(2,7)]
print("Omega in a+C:",all(sum(i in X for i in o)%2==1 and sum(i in Y for i in o)%2==1 for o in Om),"W=6 <= 4n-7k =",4*n-7*k)
print("parity of |Omega_i| vs k:",[len(o)%2 for o in Om],k%2)
