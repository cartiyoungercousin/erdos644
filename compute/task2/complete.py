r"""Complete families C(N,k) = all k-subsets of [N], N = ceil(7k/4), k = 1 mod 4, T = N - k (so tau = T+1 > T, 4T = 3k+1).
Checks (exact SAT, pysat CaDiCaL; every SAT model re-checked in plain code):
 (1) [cited, FRESH_C 14.1] (7,2): seven sets of size <= T on [N] cannot cover all pairs (x = y allowed)  -> UNSAT expected;
 (2) saturation: one set of size T+1 and six of size <= T can cover all pairs       -> SAT expected
     (one incidence class: Sym(N) is transitive on (B, z)). Then C(N,k) is locally minimal
     (deletion: co-edge K_B is the unique co-edge containing the T-set K_B, so Lemma 3 holds with S_B = K_B).
Usage: py -3.14 complete.py"""
import itertools
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType

def cover(N, sizes):
    m = len(sizes); v = lambda x, i: x * m + i + 1; top = N * m
    s = Cadical153(); cls = []
    for x, y in itertools.combinations_with_replacement(range(N), 2):
        lits = []
        for i in range(m):
            if x == y: lits.append(v(x, i)); continue
            top += 1; a = top; cls += [[-a, v(x, i)], [-a, v(y, i)]]; lits.append(a)
        cls.append(lits)
    for i, sz in enumerate(sizes):
        c = CardEnc.atmost([v(x, i) for x in range(N)], bound=sz, top_id=top, encoding=EncType.seqcounter)
        top = max(top, c.nv); cls += c.clauses
    # symmetry: point 0 in set 0
    cls.append([v(0, 0)])
    for c in cls: s.add_clause(c)
    if not s.solve(): return None
    mod = set(l for l in s.get_model() if l > 0)
    sets = [{x for x in range(N) if v(x, i) in mod} for i in range(m)]
    assert all(len(S) <= sz for S, sz in zip(sets, sizes))
    for x, y in itertools.combinations_with_replacement(range(N), 2):
        assert any(x in S and y in S for S in sets)
    return sets

for k in (5, 9, 13):
    N = -(-7 * k // 4); T = N - k
    sat = cover(N, [T + 1] + [T] * 6)   # (7,2) of C(N,k): cited from notes/FRESH_C.md 14.1 (exact ILP), not re-run here
    print(f"k={k} N={N} T={T} t={T/k:.3f}: "
          f"saturation {'certificate ' + str([sorted(S) for S in sat]) if sat else 'LOOSE (UNSAT)'}", flush=True)
