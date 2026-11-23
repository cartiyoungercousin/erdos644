r"""Randomized sanity check of the Fano template lemma, in its 'tight triple' form:

  E,F,G edges with empty common intersection, U = E u F u G.  Give every point of U a class in
  {x1,x2,y1,y2,z1,z2}:  X=E^F -> x*,  Y=E^G -> y*,  Z=F^G -> z*,  P_E -> x* or y*,  P_F -> x* or z*,
  P_G -> y* or z*  (each class pair split evenly).  The four requests are the 'even' triples
  x_c u y_b u z_a (a+b+c even); each has about |U|/2 points.
  Claim: E,F,G plus ANY four edges avoiding the four requests have no 2-point transversal.
Responses here are random k-sets avoiding the request and are allowed to use brand-new points.
"""
import random, itertools

def has_2cover(sets, pts):
    pts = list(pts)
    for i, u in enumerate(pts):
        for v in pts[i:]:
            if all(u in S or v in S for S in sets): return True
    return False

def trial(k, rng):
    # random good triple: choose pair-cell sizes x,y,z with x+y<=k etc.
    while True:
        x, y, z = (rng.randint(0, k) for _ in range(3))
        if x + y <= k and x + z <= k and y + z <= k: break
    it = itertools.count()
    take = lambda m: [next(it) for _ in range(m)]
    X, Y, Z = take(x), take(y), take(z)
    PE, PF, PG = take(k - x - y), take(k - x - z), take(k - y - z)
    E, F, G = set(X + Y + PE), set(X + Z + PF), set(Y + Z + PG)
    U = E | F | G
    cls = {}
    def put(points, options):
        for p in points: cls[p] = None, options
    groups = {"x": [], "y": [], "z": []}
    for p in X: groups["x"].append(p)
    for p in Y: groups["y"].append(p)
    for p in Z: groups["z"].append(p)
    for p in PE: groups[rng.choice("xy")].append(p)
    for p in PF: groups[rng.choice("xz")].append(p)
    for p in PG: groups[rng.choice("yz")].append(p)
    half = {}
    for g, pts in groups.items():
        rng.shuffle(pts); h = len(pts) // 2
        half[g, 0], half[g, 1] = set(pts[:h]), set(pts[h:])
    sets = [E, F, G]; maxreq = 0
    newpool = list(range(10**6, 10**6 + 4 * k))
    for (c, b, a) in [(0,0,0), (0,1,1), (1,0,1), (1,1,0)]:
        D = half["x", c] | half["y", b] | half["z", a]
        maxreq = max(maxreq, len(D))
        free = [p for p in U if p not in D] + newpool
        sets.append(set(rng.sample(free, k)))
    allpts = set().union(*sets)
    return has_2cover(sets, allpts), maxreq, len(U)

if __name__ == "__main__":
    rng = random.Random(7); bad = 0; worst = 0
    for k in [4, 6, 8, 12, 16]:
        for _ in range(400):
            c, m, u = trial(k, rng); bad += c; worst = max(worst, m - u / 2)
    print("tuples with a 2-cover (should be 0):", bad, "| max (request size - |U|/2):", worst)
