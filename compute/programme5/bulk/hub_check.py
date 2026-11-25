"""Brute-force test of the HUB lemma (non-Fano three-anchor finish), small random instances.
Pencil x_a,x_b,x_c (k-sets, empty triple intersection), D = pairwise-only parts, E_i private parts.
Blocks: L_0 = D + spill, L_i = D_jl + (E_i - spill_i), spill_i = max(0, |E_i|+|D_jl|-T). Claim: if |D| + sum spill <= T,
every block has <= T points and every pair meeting all three anchors lies in a block; hence with any k-sets
B_g disjoint from L_g (they exist in a T-covering family), the seven {x_a,x_b,x_c,B_0..B_3} have no 2-point
transversal. Equivalent condition: |D| <= T and sum_i max(0, d_ij+d_il-d_jl-(k-T)) <= 4T-3k.
usage: py -3.14 hub_check.py TRIALS SEED"""
import sys, random, itertools
def run(trials, seed):
    rng = random.Random(seed); tested = 0; fails = 0; eqfail = 0
    for _ in range(trials):
        k = rng.randint(3, 12); n = rng.randint(2 * k, 4 * k); T = rng.randint((3 * k) // 4, k)
        V = list(range(n))
        xa = set(rng.sample(V, k)); xb = set(rng.sample(V, k))
        rest = [v for v in V if not (v in xa and v in xb)]
        if len(rest) < k: continue
        xc = set(rng.sample(rest, k))
        A = {'a': xa, 'b': xb, 'c': xc}
        Dbc = (xb & xc) - xa; Dac = (xa & xc) - xb; Dab = (xa & xb) - xc
        Ea = xa - xb - xc; Eb = xb - xa - xc; Ec = xc - xa - xb
        D = Dab | Dac | Dbc
        pairs = [(Ea, Dbc), (Eb, Dac), (Ec, Dab)]
        sp = [max(0, len(E) + len(X) - T) for E, X in pairs]
        cond = len(D) + sum(sp) <= T
        d = dict(ab=len(Dab), ac=len(Dac), bc=len(Dbc))
        alt = len(D) <= T and (max(0, d['ab'] + d['ac'] - d['bc'] - (k - T)) + max(0, d['ab'] + d['bc'] - d['ac'] - (k - T))
                                + max(0, d['ac'] + d['bc'] - d['ab'] - (k - T))) <= 4 * T - 3 * k
        if cond != alt: eqfail += 1
        if not cond: continue
        L0 = set(D); Ls = []
        for (E, X), s in zip(pairs, sp):
            El = sorted(E); L0 |= set(El[:s]); Ls.append(set(X) | set(El[s:]))
        blocks = [L0] + Ls
        tested += 1
        ok = all(len(L) <= T for L in blocks)
        for x, y in itertools.combinations_with_replacement(V, 2):
            if all((x in S or y in S) for S in A.values()):
                if not any(x in L and y in L for L in blocks): ok = False
        if n - T >= k:
            Bs = [set(rng.sample([v for v in V if v not in L], k)) for L in blocks]
            seven = [xa, xb, xc] + Bs
            for x, y in itertools.combinations_with_replacement(V, 2):
                if all((x in S or y in S) for S in seven): ok = False
        if not ok:
            fails += 1; print('FAIL', k, n, T, d)
    print('instances satisfying the HUB condition: %d, failures: %d, condition-equivalence mismatches: %d' % (tested, fails, eqfail))
run(int(sys.argv[1]), int(sys.argv[2]))
