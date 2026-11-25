r"""CORE 55: the two-ground pencil question for greedy rules with R classes, exact (SAT).
Greedy rule: class c has a linear order; reply to a T-set S of class c = S + first omega points of V\S in that order.
Variables: class of every T-set.  m_K = "co-edge K is a member" (parent criterion 55.1: K = S + head_c(S), sigma(S) = c).
Clauses: sigma(S)=c -> m_{K_c(S)};  for every perfect pencil frame (kernel n-3k/2, three petals k/2): not all three lines members.
SAT  <=> some selector makes the family pencil-free (for these orders).  UNSAT <=> every selector leaves a pencil.
Usage: py two_ground_sat.py k T n R mode [seed]    mode: rev (order 2 = reverse of order 1; R=2), rand, shift
"""
import itertools, sys, time, random
from pysat.solvers import Cadical153

def three_partitions(X, h):
    first = X[0]
    for A in itertools.combinations(X[1:], h - 1):
        P1 = (first,) + A; s1 = set(P1)
        rest = [x for x in X if x not in s1]
        f2 = rest[0]
        for B in itertools.combinations(rest[1:], h - 1):
            P2 = (f2,) + B; s2 = set(P2)
            yield P1, P2, tuple(x for x in rest if x not in s2)

def mask(t):
    m = 0
    for x in t: m |= 1 << x
    return m

def run(k, T, n, R, mode, seed=0):
    om = n - k - T; ker = n - 3 * k // 2; h = k // 2; rng = random.Random(seed)
    if mode == "rev": orders = [list(range(n)), list(range(n - 1, -1, -1))][:R]
    elif mode == "shift": orders = [[(x + c * (n // R)) % n for x in range(n)] for c in range(R)]
    else: orders = [rng.sample(range(n), n) for _ in range(R)]
    t0 = time.time(); s = Cadical153(); nv = 0
    sig = {}; mem = {}
    def mv(K):
        nonlocal nv
        if K not in mem: nv += 1; mem[K] = nv
        return mem[K]
    sure = 0
    for S in itertools.combinations(range(n), T):
        ms = mask(S); Ks = []
        for o in orders:
            K = ms; c = 0
            for x in o:
                if not (ms >> x) & 1:
                    K |= 1 << x; c += 1
                    if c == om: break
            Ks.append(K)
        vs = []
        for c in range(R):
            nv += 1; vs.append(nv); s.add_clause([-nv, mv(Ks[c])])
        s.add_clause(vs)
        if len(set(Ks)) == 1: sure += 1
    nf = 0
    for kap in itertools.combinations(range(n), ker):
        mk = mask(kap); X = [x for x in range(n) if not (mk >> x) & 1]
        for P in three_partitions(X, h):
            L = [mk | mask(p) for p in P]
            if all(l in mem for l in L):
                s.add_clause([-mem[l] for l in L]); nf += 1
    ok = s.solve()
    print(f"k={k} T={T} n={n} om={om} R={R} {mode} seed={seed}: {len(mem)} reachable co-edges, {sure} class-independent requests, "
          f"{nf} reachable frames; pencil-free selector exists: {ok}  ({time.time()-t0:.0f}s)", flush=True)
    return ok

if __name__ == "__main__":
    a = sys.argv
    run(int(a[1]), int(a[2]), int(a[3]), int(a[4]), a[5], int(a[6]) if len(a) > 6 else 0)
