r"""Densities p = |H|/C(n,k) of the CORE 56 greedy families (members = complements of replies, H = {V - reply(S)}).
B is a member iff for some class c and some omega-set H' inside P_c(B) = {points before min_c(B) in order c},
the request S = V - B - H' has sel(S) = c (then reply(S) = S + H' = V - B).
(1) hash selectors: closed form, treating sel(S) as independent uniform per (S, c) [exact up to the rare
    coincidence of one S being a candidate for two classes]:  p = 1 - (E[(1 - 1/R)^{C(L, omega)}])^R,
    P(L >= m) = C(n-m, k)/C(n, k).
(2) every selector kind: Monte Carlo membership with the rule code of compute/core9/hash_check.py verbatim.
Usage: py -3.14 gamma_hash.py [samples]
"""
import sys, os, random, math
from math import comb, log
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "core9"))
from hash_check import Rule, make_selector
from itertools import combinations

def p_hash(n, k, T, R):
    om = n - k - T; tot = comb(n, k)
    E = 0.0
    for L in range(0, n - k + 1):
        pr = (comb(n - L, k) - comb(n - L - 1, k)) / tot          # P(L = exactly L)
        if pr == 0: continue
        E += pr * (1 - 1 / R) ** comb(L, om)
    return 1 - E ** R

def member(rule, B, R):
    n, om = rule.n, rule.om; Bs = set(B)
    for c in range(R):
        P = []
        for x in rule.orders[c]:
            if x in Bs: break
            P.append(x)
        if len(P) < om: continue
        for Hp in combinations(P, om):
            S = frozenset(range(n)) - Bs - set(Hp)
            if rule.sel(rule, S) == c:
                assert rule.reply(S) == frozenset(range(n)) - Bs
                return True
    return False

if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
    sizes = [(40, 31, 74), (40, 31, 76), (40, 31, 80), (40, 31, 88), (100, 76, 180), (100, 76, 190), (100, 76, 210)]
    print("closed form, hash selectors: gamma = ln(1/p)/k;  gamma_a = ln C(n-T, k)/k (minimal covering)")
    for (k, T, n) in sizes:
        ga = log(comb(n - T, k)) / k
        row = [f"R={R}: p={p_hash(n,k,T,R):.3e} gamma={-log(p_hash(n,k,T,R))/k:.4f}" for R in (2, 8, 64)]
        print(f"k={k} T={T} n={n} N={n/k:.3f} omega={n-k-T}  gamma_a={ga:.4f} | " + " | ".join(row))
    print(f"\nMonte Carlo ({M} random k-sets per rule), rule code verbatim:")
    rng = random.Random(644)
    kinds = [("hash", 2), ("hash", 8), ("hash", 64), ("linear", 2), ("linear", 8), ("parity", 2), ("parity", 8), ("early", 2),
             ("early", 4), ("late", 2), ("late", 4), ("early^hash", 2), ("early^hash", 4), ("junta+", None), ("midhash", 2), ("midhash", 4)]
    for (k, T, n) in [(40, 31, 74), (100, 76, 180)]:
        for kind, R in kinds:
            RR = R if R else T - k // 2 + 2
            orders = [rng.sample(range(n), n) for _ in range(RR)]
            rule = Rule(n, k, T, orders, make_selector(kind, n, k, T, RR, rng))
            hits = sum(member(rule, rng.sample(range(n), k), RR) for _ in range(M))
            p = hits / M
            g = (-log(p) / k) if hits else float("inf")
            print(f"k={k} n={n} {kind:10s} R={RR:3d}: p~{p:.4f} ({hits}/{M})  gamma~{g:.4f}", flush=True)
