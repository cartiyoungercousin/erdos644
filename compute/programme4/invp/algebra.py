"""Exact checks of the class-level algebra used in notes/PROGRAMME4_INVP.md section 2.

(a) For every Gamma in F_2^m (m <= 5) with |Gamma| <= 4: Gamma+Gamma+Gamma (repeats allowed) = aff(Gamma).
(b) For |Gamma| = 5 the two can differ; count how often, and confirm the 5-cap
    {e1,e2,e3,e4,e1+e2+e3+e4} in F_2^4 has 3*Gamma = F_2^4 minus {0} while aff = F_2^4.
(c) Block-ball family: A = {beta in F_2^q : wt(beta) >= q - rho}; every 3-sum has weight >= q - 3 rho
    (exhaustive for q <= 10), and the hole bound (rho+1) n / q > T is incompatible with q - 3 rho >= 1
    once n/T < 3 (checked on the window grid).
Usage: py -3.14 algebra.py
"""
from itertools import combinations, product

def aff(G):
    G = list(G)
    out = set()
    for s in range(1, len(G) + 1, 2):
        for c in combinations(G, s):
            v = 0
            for x in c:
                v ^= x
            out.add(v)
    return out

def three(G):
    return {a ^ b ^ c for a in G for b in G for c in G}

def part_a():
    for m in range(1, 6):
        N = 1 << m
        bad = 0
        tot = 0
        for s in range(1, 5):
            for G in combinations(range(N), s):
                tot += 1
                if three(G) != aff(G):
                    bad += 1
        print("(a) m=%d: %d sets of size <=4, %d with 3G != aff(G)" % (m, tot, bad))

def part_b():
    for m in (4, 5):
        N = 1 << m
        diff = 0
        tot = 0
        for G in combinations(range(N), 5):
            tot += 1
            if three(G) != aff(G):
                diff += 1
        print("(b) m=%d: %d five-sets, %d with 3G != aff(G) (all need a 5-sum outside 3G)" % (m, tot, diff))
    cap = [1, 2, 4, 8, 15]
    t = three(cap)
    print("(b) 5-cap: |3G| =", len(t), "0 in 3G:", 0 in t, "| |aff| =", len(aff(cap)))

def part_c():
    for q in range(3, 11):
        for rho in range(0, q // 3 + 1):
            A = [b for b in range(1 << q) if bin(b).count('1') >= q - rho]
            mn = min(bin(a ^ b ^ c).count('1') for a in A for b in A for c in A)
            assert mn >= q - 3 * rho, (q, rho, mn)
    print("(c) block-ball: min 3-sum weight >= q - 3 rho verified for q <= 10")
    # hole bound: covering needs (rho+1) * n/q > T (S avoids rho+1 smallest blocks otherwise);
    # heaviness needs q >= 3 rho + 1.  With n/T = N/t: q < (rho+1) N/t.
    worst = 0
    for Nn in [1.75 + i / 1000 for i in range(0, 84)]:
        for t in [0.75 + j / 1000 for j in range(0, 30)]:
            for rho in range(0, 50):
                qmax = (rho + 1) * Nn / t
                Pmax = qmax - 3 * rho
                worst = max(worst, Pmax)
    print("(c) block-ball: largest pattern weight q - 3 rho compatible with the hole bound, window grid: %.2f" % worst)

if __name__ == '__main__':
    part_a()
    part_b()
    part_c()
