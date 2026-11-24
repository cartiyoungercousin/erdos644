"""RED TEAM: cheap simulation of simple requesters against the proportional adversary (prop.py rule).
Requester rule 'top': request highest-degree types first (Lemma 3 / spread lemma), full budget.
Outcome: 'spread' if the 7 replies have no 2-cover at all (7-request win), else min_6 mass(D)-T (8-request game)."""
import sys
def popc(x): return bin(x).count("1")
def play(T, Ns, rule="top", eps=1e-9):
    E = len(Ns); m = {0: Ns[0] - 1.0, 1: 1.0}; real = {1}
    for e in range(1, E):
        b = 1 << e; m[0] += Ns[e] - Ns[e - 1]; lam = 1.0 / (Ns[e] - T)
        left = T; s = {}
        for J in sorted(m, key=lambda J: (-popc(J), J)):
            x = min(left, m[J]); s[J] = x; left -= x
        m2 = {}
        for J, mj in m.items():
            a = mj - s[J]; m2[J] = mj - lam * a
            if a > eps: m2[J | b] = lam * a; real.add(J | b)
        m = {J: v for J, v in m2.items() if v > eps or J == 0}
    full = (1 << E) - 1
    cov = any((A | B) == full for A in real for B in real)
    best = 9
    for drop in range(E):
        I = full & ~(1 << drop)
        D = sum(mj for J, mj in m.items() if any((K & (I & ~J)) == (I & ~J) for K in real))
        best = min(best, D - T)
    maxdeg = max(popc(J) for J in real)
    return cov, best, maxdeg
if __name__ == "__main__":
    for T in (0.76, 0.80):
        for N in (1 + T, 1.9, 2.0, 2.15, 7 / 3, 2.5, 2.75, 3.0, 3.5, 4.0, 5.0):
            cov, best, md = play(T, [N] * 7)
            print(f"T={T} N={N:.3f}: 7 replies 2-coverable={cov} maxdeg={md}  min_6 mass(D)-T={best:+.4f}  ->",
                  "REQUESTER wins (7 req)" if not cov else ("REQUESTER wins (8 req)" if best <= 1e-9 else "top-degree rule fails"))
