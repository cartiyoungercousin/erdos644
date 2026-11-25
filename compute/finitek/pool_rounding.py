"""Finite-k Pool theorem P (CORE 5): rounding lemma, exhaustive test, end-to-end plays.
Usage: py -3.14 pool_rounding.py [kmax] [plays_per_case]
Hypotheses H(k,T,N,Z): 4T>=3k, k+T<=N, omega=N-k-T<=Z<=floor(N-3k/2).
Lemma R: if 4T>=3k and 4T!=3k+1 an integer plan (w, m1..m6) exists, explicit below.
"""
import sys, random, math, itertools

def plan(k, T, N, Z):
    """explicit integer plan from the proof of Lemma R; returns (w, (m1..m6)) or None"""
    c = N - k
    if Z <= N - 2 * T:                       # case A: w = N - 2T, classes x,x,y,y,z,z
        w = N - 2 * T
        q, r = divmod(T, 3)
        x, y, z = [q + (1 if i < r else 0) for i in range(3)]
        m = (x, x, y, y, z, z)
    else:                                    # case B: w = Z, balanced pairs, oriented halves
        w = Z
        M = N - w
        q, r = divmod(M, 3)
        p = [q + (1 if i < r else 0) for i in range(3)]
        best = None
        for b in itertools.product((0, 1), repeat=3):       # b_i = position of the larger half
            hs = []
            for i in range(3):
                big, small = (p[i] + 1) // 2, p[i] // 2
                hs.append((big, small) if b[i] == 0 else (small, big))
            m = (hs[0][0], hs[0][1], hs[1][0], hs[1][1], hs[2][0], hs[2][1])
            mx = max(m[0]+m[2]+m[4], m[0]+m[3]+m[5], m[1]+m[2]+m[5], m[1]+m[3]+m[4])
            if best is None or mx < best[0]:
                best = (mx, m)
        m = best[1]
    return w, m

def plan_ok(k, T, N, Z, w, m):
    c = N - k
    m1, m2, m3, m4, m5, m6 = m
    if min(m) < 0 or w < Z or w > (2 * N - 3 * k) // 2: return False
    if w + sum(m) != N: return False
    if any(w + a + b > c for a, b in ((m1, m2), (m3, m4), (m5, m6))): return False
    if max(m1+m3+m5, m1+m4+m6, m2+m3+m6, m2+m4+m5) > T: return False
    return True

def hyp(k, T, N, Z):
    return 4*T >= 3*k and k+T <= N and N-k-T <= Z <= (2*N-3*k)//2

def play(k, T, N, Z, rnd):
    """build the 7 requests of the proof, answer with a random pool adversary, return True iff the 7 co-edges cover all pairs"""
    c = N - k; om = c - T
    w, m = plan(k, T, N, Z)
    pts = list(range(N)); rnd.shuffle(pts)
    Zset = set(pts[:Z]); rest = pts[Z:]
    Vo = set(Zset) | set(rest[:w - Z]); rest = rest[w - Z:]
    cls, pos = [], 0
    for mm in m: cls.append(set(rest[pos:pos+mm])); pos += mm
    mode = rnd.choice(['rand', 'Zlast'])
    def reply(S):
        free = [x for x in pts if x not in S]
        need = c - len(S)
        zf = [x for x in free if x in Zset]
        if len(zf) >= need: add = rnd.sample(zf, need)          # pool rule binds
        elif mode == 'Zlast':
            nz = [x for x in free if x not in Zset]; rnd.shuffle(nz); add = (nz + zf)[:need]
        else: add = rnd.sample(free, need)
        return set(S) | set(add)
    Ks = []
    for (i, j) in ((0, 1), (2, 3), (4, 5)):
        L = Vo | cls[i] | cls[j]
        Zpp = set(rnd.sample(sorted(Zset), om))
        S = L - Zpp
        assert len(S) <= T
        pad = [x for x in pts if x not in S and x not in Zpp]; rnd.shuffle(pad)
        S |= set(pad[:T - len(S)])
        assert len(S) == T and not (S & Zpp)
        K = reply(S); assert K >= L; Ks.append(K)
    for (i, j, l) in ((0, 2, 4), (0, 3, 5), (1, 2, 5), (1, 3, 4)):
        L = cls[i] | cls[j] | cls[l]; assert len(L) <= T
        K = reply(L); Ks.append(K)
    cov = [0]*N
    for jj, K in enumerate(Ks):
        assert len(K) == c
        for x in K: cov[x] |= 1 << jj
    ms = set(cov)
    return 0 not in ms and all(a & b for a in ms for b in ms)

def main():
    kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    plays = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    rnd = random.Random(7)
    tot = nplan = fail_plan = bad_play = 0
    exc = {}   # exceptional 4T=3k+1: all hypothesis instances have no plan
    exc_total = exc_noplan = 0
    for k in range(1, kmax + 1):
        for T in range(math.ceil(3*k/4), k + 4):
            for N in range(k + T, 3*k + 3):
                for Z in range(N-k-T, (2*N-3*k)//2 + 1):
                    if not hyp(k, T, N, Z): continue
                    if 4*T == 3*k + 1:
                        exc_total += 1
                        # no integer w exists in the window [max(Z,N-2T), floor(N-3k/2)] = {N-2T} with a valid plan
                        w = N - 2*T
                        found = False
                        for w in range(max(Z, N-2*T), (2*N-3*k)//2 + 1):
                            M = N - w; P = N - k - w
                            if k <= 13:
                                for m1 in range(T+1):
                                  for m2 in range(T+1-m1):
                                    for m3 in range(T+1-m1):
                                      for m4 in range(T+1-m2):
                                        for m5 in range(T+1):
                                            m6 = M-m1-m2-m3-m4-m5
                                            if m6 >= 0 and plan_ok(k, T, N, Z, w, (m1,m2,m3,m4,m5,m6)): found = True; break
                                        if found: break
                                      if found: break
                                    if found: break
                            else:   # M=2T forces the shape (x,x,y,y,z,z) (proof of Lemma R)
                                for x in range(T+1):
                                    for y in range(T+1-x):
                                        if plan_ok(k, T, N, Z, w, (x,x,y,y,T-x-y,T-x-y)): found = True
                            if found: break
                        exc_noplan += (not found)
                        continue
                    tot += 1
                    w, m = plan(k, T, N, Z)
                    if not plan_ok(k, T, N, Z, w, m): fail_plan += 1; print("PLAN FAIL", k, T, N, Z, w, m); continue
                    for _ in range(plays):
                        if not play(k, T, N, Z, rnd): bad_play += 1; print("PLAY FAIL", k, T, N, Z)
    print(f"k<={kmax}: {tot} instances with 4T>=3k, 4T!=3k+1: explicit plan valid in {tot-fail_plan}, plan failures {fail_plan}; "
          f"random pool plays x{plays}: {bad_play} failures")
    print(f"4T=3k+1 instances: {exc_total}, of which with NO integer plan: {exc_noplan}")
main()
