from qprime_sigma_density import *
for vs,pi in [([6,5],[2,3]),([6,6],[4,2]),([5,5],[3,3]),([6,6,5],[3,3,3])]:
    try: print(vs,pi,"(class,triples,regular,maxindep,density,avoidpoint)",density_test(vs,pi,0))
    except AssertionError: print(vs,pi,"parity fail")
