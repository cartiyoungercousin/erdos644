"""Q1: run the 6/7 manuscript's finishing path (Theorem 5.2, branch M <= h, with Lemma 4.8 'two large opposite
cells') against the two-cluster adversary of Theorem O (PROGRAMME5_BEAT78 §2.2), on real sets at finite k.
Adversary: disjoint R1, R2 of size s = ceil((2-c)k). Answer to U: a cluster i with |R_i - U| >= k (EVERY feasible
choice is explored), one glue point of x cap R_{3-i} - U for every earlier answer x of the other cluster, rest
filled from R_i - U preferring points lying in many earlier same-cluster answers (maximises x = |E cap F|, b = |G cap H|).
Requester: E; G := answer to T points of E; F := balanced request (Lemma 2.5) on (E,G); if |E cap F| > k/2:
H := answer to X+Y+Z + private points of G; if |G cap H| > k/2: Lemma 4.8 (I, then X+B1 and (X cap I)+(B-B1)).
Every leaf is checked by brute force: the 7 edges have no 2-point transversal.  (Static leaves, where Cor 3.2 would be
used, are only reported.)   usage: py -3.14 q1_two_cluster.py k t c [seed]"""
import sys, math, random, itertools

def run(k, t, c, seed=0):
    T = math.floor(t * k); s = math.ceil((2 - c) * k)
    R = [set(range(0, s)), set(range(s, 2 * s))]
    rng = random.Random(seed)
    leaves = []

    def answers(hist, U):
        """all adversary answers (one per feasible cluster)"""
        out = []
        for i in (0, 1):
            free = R[i] - U
            if len(free) < k: continue
            B = set()
            for (x, ci) in hist:
                if ci != i:
                    cand = sorted((x & R[1 - i]) - U)
                    if not cand: return None   # glue impossible (does not happen for k large)
                    B.add(cand[0])
            same = [x for (x, ci) in hist if ci == i]
            pool = sorted(free - B, key=lambda p: (-sum(p in x for x in same), rng.random()))
            B |= set(pool[:k - len(B)])
            assert len(B) == k and not (B & U)
            out.append((B, i))
        return out

    def no_2_transversal(edges):
        pts = sorted(set().union(*edges))
        cover = {p: frozenset(j for j, e in enumerate(edges) if p in e) for p in pts}
        full = frozenset(range(len(edges)))
        types = set(cover.values())
        return not any((a | b) == full for a in types for b in types)

    E = (set(range(k)), 0)                       # first answer: k points of R1
    for (G, gi) in answers([E], set(list(E[0])[:T])):
        hist = [E, (G, gi)]
        e, g = E[0], G
        M = len(e & g)
        Ilist = sorted(e & g); pe = sorted(e - g); pg = sorted(g - e)
        U = set(Ilist) | set(pe[:(T - M) // 2]) | set(pg[:T - M - (T - M) // 2])
        assert len(U) <= T
        for (F, fi) in answers(hist, U):
            h2 = hist + [(F, fi)]
            ef, fg = len(e & F), len(F & g)
            if ef <= k / 2 and fg <= k / 2:
                leaves.append(('static Cor3.2 on E,F,G', M, ef, fg)); continue
            # orient so that X = E' cap F is the large cell, E' in {e, g}
            if ef > k / 2: A, C = e, g          # X = A cap F, the edge C plays 'G'
            else: A, C = g, e
            X = A & F; Y = A & C; Z = F & C
            PG = sorted(C - A - F)
            x = len(X)
            U2 = X | Y | Z | set(PG[:T - len(X | Y | Z)])
            assert len(U2) <= T, (len(X | Y | Z), T)
            for (H, hi) in answers(h2, U2):
                h3 = h2 + [(H, hi)]
                B = C & H; b = len(B)
                if b <= k / 2:
                    leaves.append(('static Cor3.2 on A,C,H', len(A & C), len(A & H), b)); continue
                Y2, Z2 = Y, Z                      # E cap G, F cap G
                Yp, Zp = F & H, A & H              # F cap H, E cap H
                Uglue = Y2 | Z2 | Yp | Zp
                sig, rho = len(Y2) + len(Z2), len(Yp) + len(Zp)
                m = max(len(Y2), len(Z2), len(Yp), len(Zp))
                p = math.ceil(k / 2) - min(sig, rho); q = T - math.ceil(k / 2) - max(sig, rho)
                cond = (T >= math.ceil(k / 2) + 2 * m, T >= x + m, 3 * T >= 2 * x + b + math.ceil(k / 2) + 2 * m)
                B0 = set(sorted(B)[:p]); X0 = set(sorted(X)[:q])
                U3 = Uglue | B0 | X0
                assert len(U3) <= T
                for (I, ii) in answers(h3, U3):
                    h4 = h3 + [(I, ii)]
                    BI = B & I
                    B1 = set(BI) | set(sorted(B - BI)[:max(0, min(b, T - x) - len(BI))])
                    R1 = X | B1; R2 = (X & I) | (B - B1)
                    sizes = (len(R1), len(R2))
                    for (J1, j1) in answers(h4, R1):
                        for (J2, j2) in answers(h4 + [(J1, j1)], R2):
                            seven = [A, F, C, H, I, J1, J2]
                            ok = no_2_transversal(seven)
                            leaves.append(('Lemma4.8', x, b, m, cond, sizes, T, ok, (fi, hi, ii, j1, j2)))
    return T, leaves

if __name__ == '__main__':
    k, t, c = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    T, leaves = run(k, t, c, seed)
    print('k=%d t=%.4f T=%d c=%.4f s=%d' % (k, t, T, c, math.ceil((2 - c) * k)))
    for L in leaves: print(' ', L)
    l48 = [L for L in leaves if L[0] == 'Lemma4.8']
    print('Lemma 4.8 leaves: %d, all bad sevens: %s, all conditions: %s' % (
        len(l48), all(L[7] for L in l48), all(all(L[4]) for L in l48)))
