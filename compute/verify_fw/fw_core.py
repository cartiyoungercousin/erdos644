"""Independent referee checks for notes/PROGRAMME4_PEN.md, items (A), (B), (D).

Usage:
  py -3.14 fw_core.py residue K          # residue step for all k <= K, primes (k+1)/2 <= p <= k
  py -3.14 fw_core.py cover N            # exact identity C(n,k+r)/C(n-k,r) = C(n,k)/C(k+r,r), n <= N
  py -3.14 fw_core.py dump TRIALS SEED   # random pairs at distance 2p, every x3 in a (k+r)-subset of x1^x2
  py -3.14 fw_core.py brute              # exact max families (CP-SAT, 2 workers) vs both FW bounds
  py -3.14 fw_core.py rank               # rank check of the FW polynomial evaluation matrix over F_p
"""
import sys, random, itertools
from math import comb
from fractions import Fraction


def is_prime(m):
    if m < 2:
        return False
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return True


def residue(K):
    bad = 0
    cases = 0
    for k in range(1, K + 1):
        for p in range((k + 2) // 2, k + 1):
            if not is_prime(p) or 2 * p < k + 1:
                continue
            for i in range(0, k):  # intersections of distinct k-sets
                cases += 1
                if (i - k) % p == 0 and i != k - p:
                    bad += 1
                    print("BAD", k, p, i)
    # also show the lemma's hypothesis is needed: p = k/2 gives a second residue (intersection 0)
    extra = [(k, k // 2) for k in range(2, 40, 2) if is_prime(k // 2)]
    print(f"residue: k<={K}, {cases} (k,p,i) cases, {bad} bad")
    print("p = k/2 (excluded by hypothesis) would allow i = 0 = k-2p as well:", extra[:5])


def cover(N):
    bad = 0
    cnt = 0
    for n in range(1, N + 1):
        for k in range(0, n + 1):
            for r in range(0, n - k + 1):
                cnt += 1
                a = Fraction(comb(n, k + r), comb(n - k, r))
                b = Fraction(comb(n, k), comb(k + r, r))
                if a != b:
                    bad += 1
    print(f"cover identity: {cnt} (n,k,r), n<={N}: {bad} mismatches")


def weight(xs):
    cnt = {}
    for x in xs:
        for v in x:
            cnt[v] = cnt.get(v, 0) + 1
    return sum(1 for c in cnt.values() if c == 1), max(cnt.values())


def dump(trials, seed):
    rnd = random.Random(seed)
    bad = 0
    done = 0
    for _ in range(trials):
        k = rnd.randint(3, 40)
        r = rnd.randint(0, k // 3)
        # least prime >= (k+r+1)/2
        p = (k + r + 2) // 2
        while not is_prime(p):
            p += 1
        if p > k:
            continue
        n = k + p + rnd.randint(0, 20)  # |x1 u x2| = k+p must fit
        pts = list(range(n))
        rnd.shuffle(pts)
        common = pts[:k - p]
        x1 = set(common + pts[k - p:k])
        x2 = set(common + pts[k:k + p])
        assert len(x1) == k and len(x2) == k and len(x1 & x2) == k - p
        D = sorted(x1 ^ x2)
        assert len(D) == 2 * p >= k + r + 1
        for _ in range(5):
            A = rnd.sample(D, k + r)
            x3 = set(rnd.sample(A, k))
            w, mx = weight([x1, x2, x3])
            done += 1
            ok = (mx <= 2) and (w == 2 * p - k) and (len(x1 & x2 & x3) == 0)
            # bound with g(k) = largest gap between consecutive primes <= k:
            # note claims w <= r + 2g + 1 (sec. 2) and w <= r + 2g (sec. 0)
            ps = [q for q in range(2, k + 1) if is_prime(q)]
            g = max([b - a for a, b in zip(ps, ps[1:])] + [1])
            ok = ok and (w <= r + 2 * g)
            if not ok:
                bad += 1
                print("BAD", k, r, p, w)
    print(f"dump: {done} pencils checked, {bad} bad")


def brute():
    from ortools.sat.python import cp_model
    cases = []
    for n in range(4, 10):
        for k in range(2, n):
            for p in range(2, k + 1):
                if is_prime(p) and 2 * p >= k + 1 and k - p >= max(0, 2 * k - n):
                    if comb(n, k) <= 130:
                        cases.append((n, k, p))
    for (n, k, p) in cases:
        S = list(itertools.combinations(range(n), k))
        m = cp_model.CpModel()
        x = [m.NewBoolVar("") for _ in S]
        forb = k - p
        Ss = [set(s) for s in S]
        for i in range(len(S)):
            for j in range(i + 1, len(S)):
                if len(Ss[i] & Ss[j]) == forb:
                    m.AddBoolOr([x[i].Not(), x[j].Not()])
        m.Add(x[0] == 1)
        m.Maximize(sum(x))
        sol = cp_model.CpSolver()
        sol.parameters.num_workers = 2
        sol.parameters.max_time_in_seconds = 60
        st = sol.Solve(m)
        val = int(sol.ObjectiveValue())
        bnd = int(sol.BestObjectiveBound())
        sumb = sum(comb(n, i) for i in range(p))
        c1 = comb(n, p - 1)
        stat = "OPT" if st == cp_model.OPTIMAL else "FEAS"
        flag = "" if bnd <= sumb else "  VIOLATES_SUM"
        flag += "" if bnd <= c1 else ("  ub>C(n,p-1)" if val <= c1 else "  VIOLATES_C(n,p-1)")
        print(f"(n,k,p)=({n},{k},{p}) forbid |FnG|={forb}: max={val} [{stat}, ub {bnd}]  "
              f"sum_i<p C(n,i)={sumb}  C(n,p-1)={c1}{flag}", flush=True)


def rank():
    # For tiny (n,k,p): M[F][G] = prod_{mu in L} (|F n G| - mu) mod p over ALL k-sets.
    # Lemma FW's mechanism: restricted to a family with forbidden intersection k-p, M is diagonal
    # with (p-1)! on the diagonal. Here we check the diagonal value and the polynomial degree claim
    # by computing the rank of the evaluation matrix of the multilinearised P_F on {0,1}^n
    # (it must be <= sum_{i<p} C(n,i)).
    import numpy as np
    for (n, k, p) in [(6, 3, 2), (7, 3, 2), (7, 4, 3), (8, 5, 3), (8, 4, 3), (9, 5, 3)]:
        L = [mu for mu in range(p) if mu != k % p]
        fact = 1
        for mu in L:
            fact = fact * ((k - mu) % p) % p
        S = list(itertools.combinations(range(n), k))
        cube = list(itertools.product([0, 1], repeat=n))
        rows = []
        for F in S:
            row = []
            for v in cube:
                t = sum(v[i] for i in F)
                val = 1
                for mu in L:
                    val = val * ((t - mu) % p) % p
                row.append(val)
            rows.append(row)
        # rank over F_p by Gaussian elimination
        M = [r[:] for r in rows]
        rk = 0
        cols = len(cube)
        for c in range(cols):
            piv = None
            for i in range(rk, len(M)):
                if M[i][c] % p:
                    piv = i
                    break
            if piv is None:
                continue
            M[rk], M[piv] = M[piv], M[rk]
            inv = pow(M[rk][c], p - 2, p)
            M[rk] = [(a * inv) % p for a in M[rk]]
            for i in range(len(M)):
                if i != rk and M[i][c] % p:
                    f = M[i][c]
                    M[i] = [(a - f * b) % p for a, b in zip(M[i], M[rk])]
            rk += 1
        dim = sum(comb(n, i) for i in range(p))
        print(f"(n,k,p)=({n},{k},{p}): diag (p-1)! mod p = {fact} (expect {p-1}); "
              f"rank of {{P_F}} on cube = {rk} <= sum_i<p C(n,i) = {dim}: {rk <= dim}")


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "residue":
        residue(int(sys.argv[2]))
    elif cmd == "cover":
        cover(int(sys.argv[2]))
    elif cmd == "dump":
        dump(int(sys.argv[2]), int(sys.argv[3]))
    elif cmd == "brute":
        brute()
    elif cmd == "rank":
        rank()
