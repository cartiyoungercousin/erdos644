"""Can seven c-subsets of an N-set cover all pairs (x=y included)?  ILP over co-types (counts n_I, I subset of [7]),
used types pairwise intersecting.  Used for Thm P with omega = 0 (c = T: adversary has no freedom, K = S)."""
import itertools, sys, pulp
def feasible(N, c, m=7):
    types=[I for r in range(1,m+1) for I in itertools.combinations(range(m),r)]
    prob=pulp.LpProblem("c",pulp.LpMinimize)
    n={I:prob.add_variable("n"+"".join(map(str,I)),0,N,"Integer") for I in types}
    z={I:prob.add_variable("z"+"".join(map(str,I)),0,1,"Integer") for I in types}
    prob+=n[types[0]]*0
    prob+=pulp.lpSum(n.values())==N
    for i in range(m): prob+=pulp.lpSum(n[I] for I in types if i in I)==c
    for I in types: prob+=n[I]<=N*z[I]
    for I,J in itertools.combinations(types,2):
        if not set(I)&set(J): prob+=z[I]+z[J]<=1
    r=prob.solve(pulp.HiGHS(msg=False))
    return str(r).split(chr(10))[0]+" sol="+str(r.has_solution)
if __name__=="__main__":
    for (k,T,N) in [(4,3,7),(5,4,9),(9,7,16),(13,10,23),(17,13,30),(6,5,11),(8,6,14),(7,6,13),(5,4,10)]:
        c=N-k
        print((k,T,N), "c=",c, feasible(N,c), flush=True)
