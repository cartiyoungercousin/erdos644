import sys, random, itertools, time
sys.path.insert(0, '.')
import kdesign as D
sys.path.insert(0, '../../petal')
import design as author

def design_fast(cells):
    nz = [i for i, (a, b) in enumerate(cells) if a > 0 and b > 0]
    best = 1e9
    for ch in itertools.product(D.PAIRS, repeat=len(nz)):
        choice = [D.PAIRS[0]] * 3
        for i, c in zip(nz, ch): choice[i] = c
        # grids with a zero side: treat as no constraint (mass 0 skip) -- lp skips m==0 sides
        v = D.lp(cells, choice)
        if v is not None and v < best: best = v
    return best

rnd = random.Random(5)
# (a) single grid vs closed form
mx = 0
for _ in range(60):
    a = rnd.random(); b = rnd.random()
    v = design_fast([(a, b), (0, 0), (0, 0)])
    mx = max(mx, abs(v - D.lstar(a, b)))
print("single grid: max |LP - L*| over 60 random (a,b) in [0,1]^2 :", mx)
# monotonicity of L*
bad = 0
for _ in range(20000):
    a = rnd.random(); b = rnd.random(); da = rnd.random() * .1; db = rnd.random() * .1
    if D.lstar(a + da, b + db) < D.lstar(a, b) - 1e-12: bad += 1
print("L* monotonicity violations:", bad)
# (b) six cells vs author's MILP
t0 = time.time(); mx = 0
for it in range(12):
    cells = [(round(rnd.random() * 0.5, 3), round(rnd.random() * 0.5, 3)) for _ in range(3)]
    v1 = design_fast(cells)
    v2 = author.design([c[0] for c in cells], [c[1] for c in cells])
    mx = max(mx, abs(v1 - v2))
    print(cells, "mine %.5f author %.5f" % (v1, v2), flush=True)
print("six cells: max diff", mx, "time", time.time() - t0)
