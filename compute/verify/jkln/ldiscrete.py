"""Discrete exact game for Theorem L at (k,T)=(4,3) and (5,4)?: fourth petal on spread triple, then K-game by brute force."""
import itertools, sys
sys.path.insert(0, '.')
import kgame as K
def run(k, T):
    out = []
    for a in itertools.product(range(0, k), repeat=3):
        p = sum(a)
        if p > T: continue
        # Theorem L hypotheses scaled: a_i <= T - k/2 ; a_i + a_j - a_l <= 3T-2k
        hyp = all(2 * x <= 2 * T - k for x in a) and all(a[i] + a[j] - a[l] <= 3 * T - 2 * k for i, j, l in ((0, 1, 2), (0, 2, 1), (1, 2, 0)))
        q = [k - p + a[i] for i in range(3)]
        # she picks r (sum T-p, r_i<=q_i) ; adversary all b
        def win_with(r):
            caps = [q[i] - r[i] for i in range(3)]
            for b in K.comps_le(k, caps):          # sum b <= k (b maximal or not; monotone)
                if not K.game(a, b, k, T): return False
            return True
        best = None
        for r in K.comps(T - p, q):
            if win_with(r): best = r; break
        out.append((a, hyp, best is not None))
        if hyp and best is None: print("THEOREM L FAILS (discrete)", a, k, T)
    print("k=%d T=%d" % (k, T), "hyp cases:", sum(1 for o in out if o[1]), "all won:", all(o[2] for o in out if o[1]),
          "non-hyp cases won/total:", sum(1 for o in out if not o[1] and o[2]), "/", sum(1 for o in out if not o[1]))
    for o in out: print("  ", o)
run(int(sys.argv[1]), int(sys.argv[2]))
