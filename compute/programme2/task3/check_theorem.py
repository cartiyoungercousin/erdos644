r"""Stress test of Theorem 9': random coset families (parity families, random codes, codes with
prescribed cell structure), random disjoint Omega's of parity k; whenever (H0)-(H4') hold the literal proof
construction must succeed and pass the exact verifier.  Usage: py -3.14 check_theorem.py seed count"""
import sys, random, json
from core import Coset, rank, popc, verify_seven, evenise
from proof_mode import hypotheses, construct_proof

def rand_instance(rng):
    kind = rng.choice(['parity', 'random', 'cells'])
    if kind == 'parity':
        q = rng.randint(1, 5); sizes = [rng.randint(3, 40) for _ in range(q)]; free = rng.choice([0, 0, 2, 4, 7])
        n = sum(sizes) + free; rows = []; o = 0
        for s in sizes: rows.append(((1 << s) - 1) << o); o += s
        cs = Coset(n, rows, (1 << q) - 1, f'parity{sizes}+{free}')
    else:
        n = rng.randint(20, 120); r = rng.randint(1, 5)
        if kind == 'random':
            rows = [rng.getrandbits(n) for _ in range(r)]
        else:   # few classes with very unequal sizes: points get classes from a small random palette
            pal = [rng.randrange(1 << r) for _ in range(rng.randint(1, 6))]
            cl = [rng.choice(pal) for _ in range(n)]
            rows = [sum(((cl[x] >> i) & 1) << x for x in range(n)) for i in range(r)]
        if rank(rows) == 0: return None
        cs = Coset(n, rows, rng.randrange(1, 1 << r), f'{kind} n={n} r={r}')
    return cs

def rand_omegas(cs, k, rng):
    """three disjoint random members of a+C (each grown greedily from random points), parity k"""
    ce = evenise(cs, k); pts = list(range(cs.n)); rng.shuffle(pts); used = 0; Os = []
    cells = {}
    for x in pts: cells.setdefault(ce.cls(x), []).append(x)
    for _ in range(3):
        # random small subset with class alpha: random walk over cells
        for attempt in range(200):
            size = rng.randint(1, 8); O = 0
            avail = [x for x in pts if not (used >> x & 1)]
            if len(avail) < size: return None
            for x in rng.sample(avail, size): O |= 1 << x
            if ce.syn(O) == ce.alpha: break
        else: return None
        Os.append(O); used |= O
    return Os

if __name__ == '__main__':
    seed, count = int(sys.argv[1]), int(sys.argv[2]); rng = random.Random(seed)
    tested = ok = 0; hypfail = {}
    while tested < count:
        cs = rand_instance(rng)
        if cs is None: continue
        lo, hi = max(4, (4 * cs.n - 40) // 7), (4 * cs.n) // 7
        if lo > hi: continue
        k = rng.randint(lo, hi)
        Os = rand_omegas(cs, k, rng)
        if Os is None: continue
        ce = evenise(cs, k)
        h = hypotheses(ce, k, Os)
        if not h['all']:
            for key in ('H0', 'H1', 'H2', 'H3', 'H4'):
                if key in h and not h[key]: hypfail[key] = hypfail.get(key, 0) + 1; break
            continue
        tested += 1
        B, info = construct_proof(ce, k, Os)
        good = B is not None and verify_seven(cs, k, B)[0]
        ok += good
        if not good: print('COUNTEREXAMPLE TO PROOF', cs.name, k, info, flush=True)
    print(f'seed {seed}: hypotheses held in {tested} instances; proof construction verified in {ok}; first failing hypothesis among rejected: {hypfail}')
