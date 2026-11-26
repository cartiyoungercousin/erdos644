"""The 2x2 grid kill of the bridge seed (part 2). [computed exact, brute force]
F, G disjoint (the two cluster hubs), F = A | A', G = C | C' | L (halves; L = leftover, empty unless the
G-trace of K is below k/2), four K-type bridges K_AC = A|C|Q, K_AC' = A|C'|Q, K_A'C = A'|C|Q, K_A'C' = A'|C'|Q
(Q = shared extra points so |K| = k), and the seed bridge E (foot 3k/7 in A' subset F, foot 5k/14 in C' subset G,
3k/14 private points). Checks: every pairwise intersection is in spectrum(k); {F,G,K x4} is a good SIX
(brute force over all pairs x<=y of V), hence {E,F,G,K x4} a good seven."""
from part2_lib import spectrum, check_seven, cotype_summary, record
import itertools

out = open("logs/part2_grid_kill.log", "w")
def log(*s):
    msg = " ".join(map(str, s)); print(msg); out.write(msg + "\n")

for k, gtr in ((14, 7), (28, 14), (42, 20)):
    h = k // 2; pt = iter(range(10 ** 6)); take = lambda c: [next(pt) for _ in range(c)]
    A, A2 = take(h), take(k - h)
    C, C2 = take(gtr), take(gtr); L = take(k - 2 * gtr)
    Q = take(k - h - gtr)
    e1, e2 = round(3 * k / 7), round(5 * k / 14); Epriv = take(k - e1 - e2)
    n = next(pt)
    F, G = set(A + A2), set(C + C2 + L)
    K = {"K_AC": set(A + C + Q), "K_AC'": set(A + C2 + Q), "K_A'C": set(A2 + C + Q), "K_A'C'": set(A2 + C2 + Q)}
    E = set(A2[:e1] + C2[:e2] + Epriv)
    fam = {"E": E, "F": F, "G": G, **K}
    assert all(len(X) == k for X in fam.values())
    SP = set(spectrum(k))
    inter = {(a, b): len(fam[a] & fam[b]) for a, b in itertools.combinations(fam, 2)}
    ok_spec = all(v in SP for v in inter.values())
    six = [F, G] + list(K.values())
    log(f"k={k} n={n} |A|=|A'|={h} |C|=|C'|={gtr} |L|={len(L)} |Q|={len(Q)} E-feet ({e1},{e2},{k-e1-e2})")
    log("  pairwise intersections:", inter)
    log("  all in spectrum:", ok_spec, " K G-trace/k =", round(gtr / k, 4), " record tau =", record(k))
    log("  {F,G,4K} good six (brute force):", check_seven(six, n), "; {E,F,G,4K} good seven:",
        check_seven([E] + six, n), "; {F,G,3K} (any 3 of the K) good:",
        any(check_seven([F, G] + list(c), n) for c in itertools.combinations(K.values(), 3)))
    cells = [("A", set(A)), ("A'", set(A2)), ("C", set(C)), ("C'", set(C2)), ("L", set(L)), ("Q", set(Q)), ("Epriv", set(Epriv))]
    log("  co-types (members 0=F,1=G,2=K_AC,3=K_AC',4=K_A'C,5=K_A'C' missing the point):",
        {c: d for c, d in cotype_summary(six, cells, n).items() if d})
out.close()
