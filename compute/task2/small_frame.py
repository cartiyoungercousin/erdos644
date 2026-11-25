r"""Task 2 tests (a)-(c) on small locally-minimal counterexamples (exhaustive over all Lemma-4 witnesses).
Families: random (7,2)-families with tau > T on [n], reduced to local minimality (no member removal, no point deletion
keeps a counterexample) with compute/verify/minframe.py. Local minimality is all Lemmas 3-4 use.
For each member B (co-edge K), each z in B, ALL witness sets F (<= 6 other members, Lemma 4 (i)+(ii)) are listed, and
U = U(F) = union of the 2-transversals of F. Reported per family:
 (a) forced core  P_B = points of K in U_{z,F} for every z and every witness F; the minimum over choice functions
     z -> F(z) of |cap_z (U_{z,F(z)} - z)|; minimal private sets S_K and min/max |S_K cap U_{z,F}|.
 (b) budget of each enlarged seven {B - z} + F: (m-3) n - sum |members|  (>= -(# co-type-2 points), see TASK2 B.1),
     and the waste actually present.
 (c) degrees; for y in B, the points w outside B with {y,w} a transversal of F + {B}.
Usage: py -3.14 small_frame.py k T n trials seed"""
import sys, itertools, random, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "verify"))
import minframe as mf

def two_tr(fam, V):
    return [(a, b) for a in V for b in V if a <= b and all(a in C or b in C for C in fam)]

def analyse(H, T, out):
    V = sorted(mf.Vof(H)); n = len(V); Hl = list(H); mem = len(Hl)
    out(f"family: n={n} members={mem} sizes={sorted(len(B) for B in Hl)} total={sum(map(len, Hl))} "
        f"tau={mf.tau(Hl, V)}")
    deg = {x: sum(x in B for B in Hl) for x in V}
    out(f"  degrees {sorted(deg.values())}")
    res = {"core": [], "minint": [], "budget": [], "waste": [], "privint": []}
    for i, B in enumerate(Hl):
        K = [x for x in V if x not in B]; oth = [j for j in range(mem) if j != i]
        priv = []
        for r in range(T + 1):
            for S in itertools.combinations(K, r):
                if all(set(S) & Hl[j] for j in oth) and not any(set(P) <= set(S) for P in priv): priv.append(S)
        wit = {}
        for z in sorted(B):
            if len(B) < 2: continue
            wl = []
            for r in range(2, 7):
                for sub in itertools.combinations(oth, r):
                    F = [Hl[j] for j in sub]
                    if mf.has2([B - {z}] + F, V): continue
                    tr = two_tr([B] + F, V)
                    assert tr and all(set(x) & B == {z} for x in tr)       # Lemma 4 (ii), (7,2)
                    U = set(itertools.chain.from_iterable(two_tr(F, V)))
                    assert z in U and U <= set(K) | {z} and len(U) >= T + 1   # Cor 5
                    assert all(U & C for C in Hl)                             # U is a transversal of H
                    m = len(F) + 1; tot = len(B) - 1 + sum(map(len, F))
                    Is = {x: [t for t, C in enumerate([B - {z}] + F) if x not in C] for x in V}
                    waste = sum(len(I) - 3 for I in Is.values())
                    assert waste == (m - 3) * n - tot
                    ws = sorted({b if a == z else a for a, b in tr if z in (a, b)} - {z})
                    wl.append((sub, U, (m - 3) * n - tot, sum(len(I) == 2 for I in Is.values()), ws))
            assert wl, "Lemma 4 fails"
            wit[z] = wl
        if not wit: continue
        allU = [w[1] for wl in wit.values() for w in wl]
        core = set(K).intersection(*allU)
        # min over choice functions of |cap_z (U - z)|, brute force over distinct U's
        cand = [list({frozenset(w[1] - {z}) for w in wl}) for z, wl in wit.items()]
        best = None; prod = 1
        for c in cand: prod *= len(c)
        if prod <= 200000:
            for ch in itertools.product(*cand):
                s = len(frozenset.intersection(*ch)); best = s if best is None else min(best, s)
        pi = [len(set(S) & w[1]) for S in priv for wl in wit.values() for w in wl]
        res["core"].append(len(core)); res["minint"].append(best)
        res["budget"] += [w[2] for wl in wit.values() for w in wl]; res["privint"] += pi
        out(f"  B={sorted(B)} |K|={len(K)} omega_K={len(K)-T} private(min.)={[list(S) for S in priv]} "
            f"#wit={[len(wit[z]) for z in wit]} |U| range=({min(map(len,allU))},{max(map(len,allU))}) "
            f"forced core={sorted(core)} min|cap(U_z - z)|={best} |S cap U| range=({min(pi) if pi else '-'},"
            f"{max(pi) if pi else '-'}) budget min={min(w[2] for wl in wit.values() for w in wl)} "
            f"cotype2 max={max(w[3] for wl in wit.values() for w in wl)}")
        for z, wl in wit.items():
            out(f"     z={z} deg={deg[z]} partners w (outside B) over witnesses: {sorted({tuple(w[4]) for w in wl})}")
    return res

if __name__ == "__main__":
    k, T, n, trials, seed = map(int, sys.argv[1:6])
    rnd = random.Random(seed); seen = set()
    log = open(f"logs/small_{k}_{T}_{n}_s{seed}.log", "w")
    def out(s): print(s, flush=True); log.write(s + "\n"); log.flush()
    fams = mf.random_ces(n, k, T, trials, seed)
    out(f"k={k} T={T} n={n}: {len(fams)} random counterexamples")
    for F in fams:
        H = mf.reduce_local([frozenset(B) for B in F], T, rnd)
        c = tuple(sorted(tuple(sorted(B)) for B in H))
        if c in seen: continue
        seen.add(c)
        assert mf.is_ce(H, T) and mf.local_min(H, T)
        analyse(H, T, out)
