"""NC0(b): xi-dense (xi < 1/7) k-uniform H[W] with w >= (7k+18)/4, plus random outside members -> good seven must exist.
NC0(a): (W,d)-complete with 4w >= 7(k+d)+18 -> good seven must exist. Deletions are random or structured."""
import itertools, random, sys, json, math
from nc_verify import good_seven, is_complete, gen_W_part, gen_outside, pc
rng = random.Random(int(sys.argv[1])); res = dict(b_inst=0, b_ok=0, a_inst=0, a_ok=0, fail=[])
for it in range(int(sys.argv[2])):
    k = rng.randint(3, 5); w = math.ceil((7 * k + 18) / 4) + rng.randint(0, 1); w = min(w, 14)
    if 4 * w < 7 * k + 18: continue
    allk = [sum(1 << v for v in S) for S in itertools.combinations(range(w), k)]
    budget = (len(allk) - 1) // 7          # remove at most floor((C-1)/7) < C/7 sets
    style = rng.choice(["random", "pair", "triple-meet", "half"])
    if style == "random": rem = set(rng.sample(allk, budget))
    elif style == "pair": p = (1 << 0) | (1 << 1); rem = {m for m in allk if m & p == p}
    elif style == "triple-meet": T3 = 0b111; rem = {m for m in allk if pc(m & T3) >= 2}
    else: h = (1 << (w // 2)) - 1; rem = {m for m in allk if pc(m & h) >= k - 1}
    if len(rem) > budget: rem = set(rng.sample(sorted(rem), budget))
    H = [m for m in allk if m not in rem] + gen_outside(w, 4, k, rng, rng.choice(["random", "bigW", "pure"]), rng.randint(0, 15))
    V = 0
    for B in H: V |= B
    res["b_inst"] += 1
    if good_seven(H, V) is not None: res["b_ok"] += 1
    else: res["fail"].append(("b", k, w, style))
    # NC0(a)
    k = rng.randint(3, 5); d = rng.choice([0, 1]); w = math.ceil((7 * (k + d) + 18) / 4)
    if w > 14: continue
    HW = gen_W_part(w, k, d, rng.choice(["random", "parity", "cells"]), rng)
    assert is_complete(HW, list(range(w)), k, d)
    H = HW + gen_outside(w, 4, k, rng, "random", rng.randint(0, 10)); V = 0
    for B in H: V |= B
    res["a_inst"] += 1
    if good_seven(H, V) is not None: res["a_ok"] += 1
    else: res["fail"].append(("a", k, d, w))
print(json.dumps(res))
