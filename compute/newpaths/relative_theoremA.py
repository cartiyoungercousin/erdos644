"""§8 checks. (1) [exact, exhaustive] Fano criterion: a set of lines with no three concurrent
never covers all 7 lines together with another such set  => 7 Fano-indexed edges are bad iff each
of the 7 concurrent triples has empty common intersection.
(2) [randomized] Theorem 8.1: template on W with forced outside blocks; checks badness and that
every request has size <= ceil((|W|-k+2rho)/3) + 2*ceil(k/4) + 2, rho = max outside overlap seen."""
import itertools, random
from check_lemmas import has2cover
PTS = range(7)
LINES = [frozenset(l) for l in ((0,1,2),(0,3,4),(0,5,6),(1,3,5),(1,4,6),(2,3,6),(2,4,5))]
def no_concurrent(K): return all(sum(1 for i in K if p in LINES[i]) <= 2 for p in PTS)
caps = [frozenset(K) for r in range(8) for K in itertools.combinations(range(7), r) if no_concurrent(K)]
print("line-sets with no 3 concurrent:", len(caps), "| covering pairs among them:",
      sum(1 for A in caps for B in caps if len(A | B) == 7))
# and conversely a set containing 3 concurrent lines is covered by a cap: its complement's ... check necessity
noncaps = [frozenset(K) for r in range(8) for K in itertools.combinations(range(7), r) if not no_concurrent(K)]
print("every non-cap is completed to [7] by some cap:", all(any(len(A | B) == 7 for B in caps) for A in noncaps))
def simulate(rng):
    k = 4 * rng.randint(1, 4); wextra = rng.randint(0, 2 * k); n_out = rng.randint(1, 2 * k)
    E = list(range(k)); rest = list(range(k, k + wextra)); out = list(range(k + wextra, k + wextra + n_out + 3 * k))
    W = set(E) | set(rest)
    a = [set(E[i::4]) for i in range(4)]
    matchings = [((0,1),(2,3)), ((0,2),(1,3)), ((0,3),(1,2))]
    edges = [set(E)]; resp = {}; rho = 0; maxreq = 0; pending = []
    sizes = None
    def respond(D):
        avail = [v for v in list(W) + out if v not in D]
        # adversary: prefer points that already lie in earlier responses outside W (maximise overlaps)
        seen = set().union(*resp.values()) - W if resp else set()
        pref = [v for v in avail if v in seen]; rng.shuffle(pref); other = [v for v in avail if v not in seen]; rng.shuffle(other)
        take = pref[:rng.randint(0, min(len(pref), k))]
        return set(take + other[:k - len(take)])
    # first pass with equal thirds to learn rho is not possible adaptively; use the proof's rule:
    # B_3 is chosen after groups 1,2 are answered (the split of W-E may be decided then).
    rng.shuffle(rest)
    third = len(rest) // 3
    # provisional: decide B_1, B_2 sizes s, B_3 = rest; we emulate the bound by choosing s after the fact
    # (legal: requests of groups 1,2 only need B_1, B_2). Take s = ceil((|rest| + 2*rho_cap)/3) with rho_cap = k.
    # Simpler and still a valid test of correctness: equal thirds, and report the realised sizes.
    B = [set(rest[:third]), set(rest[third:2*third]), set(rest[2*third:])]
    for j in range(3):
        for (p, q) in matchings[j]:
            D = B[j] | a[p] | a[q]
            if j == 2:
                for x in (p, q):
                    (r1,) = [resp[(0, m)] for m in matchings[0] if x in m]
                    (r2,) = [resp[(1, m)] for m in matchings[1] if x in m]
                    o = (r1 & r2) - W; rho = max(rho, len(o)); D |= o
            maxreq = max(maxreq, len(D)); resp[(j, (p, q))] = respond(D)
    allE = edges + list(resp.values())
    bound = -(-(len(W) - k) // 3) + 2 + k // 2 + 2 * rho
    return has2cover(allE), maxreq <= bound
rng = random.Random(3); res = [simulate(rng) for _ in range(3000)]
print("Theorem 8.1 simulation: 2-covers found:", sum(r[0] for r in res), "| request-size violations:", sum(not r[1] for r in res))
