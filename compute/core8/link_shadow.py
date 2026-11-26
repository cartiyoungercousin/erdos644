"""CORE Part X (§50-§54): cluster form of the pencil and the link-shadow criterion (D).

  py link_shadow.py exp            exponents (float): random-like covering families have exp(+c k) pencil triples
  py link_shadow.py test [seed]    finite check at (k,T,n) = (8,7,17): shadow densities phi(A), cluster by frame sampling,
                                   then the good seven is built from the rule's ACTUAL replies and all pairs are checked.
"""
import itertools, math, random, sys


def H(*p):
    return -sum(x * math.log(x) for x in p if x > 0)


def exponents():
    print("t     N     gamma  log#frames  E[#pencil triples]  thr.beta  minR(51.4)  slackR(53.4)")
    for t in (0.76, 0.755):
        e = t - 0.75
        for N in (3 * t - 0.5 + 0.005, 1.80, 1.82, 1.85, 1.9, 2.0, 2.1, 2.2):
            if not (3 * t - 0.5 < N < 3 - t):
                continue
            w = N - 1 - t
            logM = N * H(t / N, 1 - t / N) - (N - 1) * H(t / (N - 1), 1 - t / (N - 1))   # covering bound, members
            logC = N * H(1 / N, 1 - 1 / N)
            gam = logC - logM
            fr = N * H((N - 1.5) / N, .5 / N, .5 / N, .5 / N)
            tri = 3 * logM + fr - 3 * logC
            # least number of pools: requests avoiding a fixed w-set
            minR = N * H(t / N, 1 - t / N) - (1 + t) * H(t / (1 + t), 1 / (1 + t))
            s = 4 * e / 3
            slackR = (1 + s) * H(s / (1 + s), 1 / (1 + s))
            print(f"{t:.3f} {N:.2f}  {gam:.3f}  {fr:.3f}       {tri:+.3f}             {tri/3:.3f}     {minR:.3f}       {slackR:.3f}")


def test(seed):
    rnd = random.Random(seed)
    k, T, n = 8, 7, 17
    c = n - k; om = c - T
    s = (4 * T - 3 * k - 1) // 3          # = 1
    lev = c - s
    V = list(range(n)); full = (1 << n) - 1
    bit = lambda S: sum(1 << x for x in S)
    reqs = [bit(S) for S in itertools.combinations(V, T)]
    Y1, Y2 = bit([0, 1]), bit([2, 3])

    def fill(K, order):
        for x in order:
            if bin(K).count("1") >= c: break
            K |= 1 << x
        return K

    def pool(S):
        return fill(S | Y1, V)

    hb = {}
    def twohash(S):                       # two pools, independent random selector
        if S not in hb: hb[S] = rnd.random() < 0.5
        Y = Y1 if hb[S] else Y2
        o = V[:]; random.Random(S).shuffle(o)
        return fill(S | Y, o)

    def avoidx(S):                        # pool Y1 unless the request contains point 16; then pool Y2
        return fill(S | (Y2 if S >> 16 & 1 else Y1), V)

    def rand(S):
        o = V[:]; random.Random(S * 7 + seed).shuffle(o)
        return fill(S, o)

    for name, F in (("pool", pool), ("two pools, hash selector", twohash), ("two pools, junta selector", avoidx),
                    ("random dump", rand)):
        cache = {}
        def reply(S):
            if S not in cache: cache[S] = F(S)
            return cache[S]
        mem = {reply(S) for S in reqs}
        assert all(bin(K).count("1") == c for K in mem)
        ext = set()
        for K in mem:
            for x in V:
                if K >> x & 1: ext.add(K & ~(1 << x))

        def phi(A):
            tot = hit = 0
            rest = [x for x in V if not A >> x & 1]
            for R in itertools.combinations(rest, lev - bin(A).count("1")):
                X = A | bit(R); tot += 1; hit += X in ext
            return hit / tot
        res = {}
        for lab, A in (("0", 0), ("Y1", Y1), ("Y2", Y2), ("Y1+x16", Y1 | 1 << 16), ("Y2+x16", Y2 | 1 << 16)):
            res[lab] = phi(A)
        best = max(res, key=res.get)
        A = {"0": 0, "Y1": Y1, "Y2": Y2, "Y1+x16": Y1 | 1 << 16, "Y2+x16": Y2 | 1 << 16}[best]
        msg = "  ".join(f"phi({a})={v:.3f}" for a, v in res.items())
        print(f"{name}: |C|={len(mem)}  {msg}")
        if res[best] <= 2 / 3:
            print("   (D) not certified on the tested A; no claim"); continue
        # frame sampling: kernel of n-2T = 3 points containing A if possible, lines of sizes lev, lev, lev-1
        k0 = n - 2 * T
        def certify(Ls):
            K = [next(M for M in mem if M & Ls[i] == Ls[i]) for i in (0, 1)] + [reply(Ls[2])]
            if K[0] | K[1] | K[2] != full: return None
            ker = K[0] & K[1] & K[2]
            if bin(ker).count("1") < k0: return None
            out = [x for x in V if not ker >> x & 1]
            # assign every outside point to one member containing it; all 3^(doubly covered) choices are legal,
            # try them until the four transversals fit into T (exact fit needs even cells when the kernel is n-2T)
            opts = [[i for i in range(3) if K[i] >> x & 1] for x in out]
            for choice in itertools.islice(itertools.product(*opts), 5000):
                Q = [[], [], []]
                for x, i in zip(out, choice): Q[i].append(x)
                for up in itertools.product((0, 1), repeat=3):
                    halves = [(q[:(len(q) + up[i]) // 2], q[(len(q) + up[i]) // 2:]) for i, q in enumerate(Q)]
                    trs = [[x for i in range(3) for x in halves[i][pat[i]]] for pat in ((0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0))]
                    if max(map(len, trs)) <= T:
                        seven = list(K)
                        for tr in trs:
                            seven.append(reply(bit(tr + [x for x in V if x not in tr][:T - len(tr)])))
                        ok = all(any(M >> x & 1 and M >> y & 1 for M in seven) for x in V for y in V)
                        assert ok
                        return bin(ker).count("1")
            return None

        found = None; tried = 0
        Al = [x for x in V if A >> x & 1]
        if len(Al) > k0:
            print("   |A| > n-2T at this size; frame needs a larger kernel, not sampled"); continue
        for it in range(20000):
            rest = [x for x in V if not A >> x & 1]; rnd.shuffle(rest)
            kap = Al + rest[:k0 - len(Al)]
            out = [x for x in V if x not in kap]; rnd.shuffle(out)
            a = lev - k0
            P = [out[:a], out[a:2 * a], out[2 * a:]]
            Ls = [bit(kap) | bit(p) for p in P]
            assert bin(Ls[2]).count("1") == T
            if Ls[0] in ext and Ls[1] in ext:
                tried += 1
                found = certify(Ls)
                if found: break
        if found:
            print(f"   frame {it+1}: cluster with kernel {found} >= {k0}; seven ACTUAL replies cover all pairs: True ({tried} frames tried)")
        else:
            print(f"   no certificate in 20000 samples ({tried} extendable frames)")


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "test":
        test(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    else:
        exponents()
