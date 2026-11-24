import spoil as SP, spoil_hunt as H, random
E = SP.Engine(0.76, 1.9)
m = {3:.33,5:.57,6:.33,2:.24,0:.43}; s = {2:.212,3:.062,5:.274,0:.212}
for R, pi in E.readings(3): print("old", [i+1 for i in R], pi, E.need_of(m, R, pi))
best = -9
rng = random.Random(1)
for d in E.menu(m, s, 2) + H.random_fills(E, m, s, rng, 4000):
    v, arg = E.min_need(E.step(m, s, d, 8), 4, new=3, want_arg=True)
    if v > best: best = v; print(round(v,5), SP.fmt(d), arg)
