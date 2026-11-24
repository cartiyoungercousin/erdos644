"""Check PETAL 7 structural claim: for triple-free four petals, every 2-cover of petals+3 centres is an edge of the
three grids (singles inactive), with edge covered iff some centre misses both: brute force vs formula."""
import random, itertools
def has2(sets):
    mask = {}
    for j, s in enumerate(sets):
        for x in s: mask[x] = mask.get(x, 0) | (1 << j)
    ms = sorted(set(mask.values())); full = (1 << len(sets)) - 1
    return any(ms[i] | ms[j] == full for i in range(len(ms)) for j in range(i, len(ms)))
rnd = random.Random(3); bad = 0; n = 0; cov = 0
pairs = list(itertools.combinations(range(4), 2))
for it in range(6000):
    pet = [set() for _ in range(4)]; pid = 0; cell = {}
    for (i, j) in pairs:
        c = rnd.choice([0, 0, 1, 1, 2, 3]); cell[(i, j)] = []
        for _ in range(c): pet[i].add(pid); pet[j].add(pid); cell[(i, j)].append(pid); pid += 1
    for i in range(4):
        for _ in range(rnd.choice([0, 1, 2, 3])): pet[i].add(pid); pid += 1
    if any(not p for p in pet): continue
    allp = list(range(pid + 4))
    cents = [set(rnd.sample(allp, rnd.randrange(len(allp) + 1))) for _ in range(3)]
    truth = has2([frozenset(p) for p in pet] + [frozenset(c) for c in cents])
    # formula: edge x in cell(i,j), y in cell(complement) with some centre missing both
    pred = False
    for (i, j) in [(0, 1), (0, 2), (0, 3)]:
        k, l = [m for m in range(4) if m not in (i, j)]
        for x in cell[(i, j)]:
            for y in cell[(k, l)]:
                if not any(x in c and True for c in cents) or True:
                    # covered iff every centre contains x or y
                    if all((x in c) or (y in c) for c in cents): pred = True
    n += 1; cov += truth
    if truth != pred: bad += 1
print("random instances", n, "with 2-cover", cov, "mismatches", bad)
