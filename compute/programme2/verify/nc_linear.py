"""Shift-0 linear layers: H = C n (V choose k), C = ker(P) for a random r x n parity-check P (proper code).
Report least d with (V,d)-complete, tau, Theorem-NC / NC1 hypotheses (W = V and all W = V minus <=2 points), good seven."""
import itertools, random, sys, json
from nc_verify import good_seven, tau, is_complete, find_triple, pc
rng = random.Random(int(sys.argv[1])); out = []
for it in range(int(sys.argv[2])):
    n = rng.randint(10, 14); k = rng.randint(4, min(8, n - 4)); r = rng.randint(1, 3)
    P = [rng.getrandbits(n) or 1 for _ in range(r)]
    H = [m for m in (sum(1 << v for v in S) for S in itertools.combinations(range(n), k)) if all(pc(m & p) % 2 == 0 for p in P)]
    if not H: continue
    V = 0
    for B in H: V |= B
    best = None
    for drop in range(0, 3):
        for D in itertools.combinations(range(n), drop):
            Wl = [v for v in range(n) if v not in D]; w = len(Wl); Wm = sum(1 << v for v in Wl)
            d = next((d for d in range(0, w - k + 1) if is_complete(H, Wl, k, d)), None)
            if d is None or w < k + d + 2: continue
            nc1 = find_triple(H, Wm, 2 * (w - k - d) - 3) is not None
            if best is None or (w - 2 * d) > (best[0] - 2 * best[1]): best = (w, d, nc1)
            if nc1: best = (w, d, True); break
        if best and best[2]: break
    t = tau(H, V)
    if best is None: out.append(dict(n=n, k=k, r=r, m=len(H), tau=t, note="no W with w>=k+d+2")); continue
    w, d, nc1 = best; a = max(0, 2 * k + 2 * d + 3 - w)
    thm = t > (k + 1) / 2 + a
    g = good_seven(H, V) is not None if (thm or nc1) else None
    out.append(dict(n=n, k=k, r=r, m=len(H), tau=t, w=w, d=d, NC1=nc1, thmNC=thm, good7=g))
for o in out: print(json.dumps(o))
