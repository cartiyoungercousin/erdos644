r"""Explicit permutation groups for the Rung 2 orbit searches; each is built from generators and its order checked.
  agl1(p)      : x -> a x + b on F_p                       order p(p-1)
  agl2(5)      : x -> A x + b on F_5^2                      order 25 * 480 = 12000
  psl3_4()     : PSL(3,4) on the 21 points of PG(2,4)       order 20160
  psl2(q)      : PSL(2,q) on PG(1,q), q = p or p^2          order q(q^2-1)/2   (q odd)
  pgl/psl helpers, cyclic(n).
Every group is returned as (generators, element list); elements are tuples (images of 0..n-1).
"""
import itertools


def closure(gens, n, limit=10 ** 6):
    idt = tuple(range(n)); seen = {idt}; frontier = [idt]
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                gh = tuple(h[g[x]] for x in range(n))
                if gh not in seen:
                    seen.add(gh); nxt.append(gh)
                    if len(seen) > limit: raise RuntimeError("group too large")
        frontier = nxt
    return sorted(seen)


def is_group_action_ok(G, n):
    S = set(G)
    for g in G[:50]:
        for h in G[:50]:
            assert tuple(h[g[x]] for x in range(n)) in S
    return True


# ---- finite fields: elements 0..q-1, q = p^e with e in {1,2}
class GF:
    def __init__(self, p, e=1, nonres=None):
        self.p, self.e, self.q = p, e, p ** e
        if e == 1:
            self.add = lambda a, b: (a + b) % p
            self.mul = lambda a, b: (a * b) % p
        else:  # F_p[t]/(t^2 - nonres), element a0 + a1 t encoded a0 + p a1
            assert e == 2 and nonres is not None
            assert all((x * x - nonres) % p for x in range(p)), "t^2 - nonres must be irreducible"
            self.add = lambda a, b: ((a % p + b % p) % p) + p * ((a // p + b // p) % p)

            def mul(a, b):
                a0, a1, b0, b1 = a % p, a // p, b % p, b // p
                return ((a0 * b0 + nonres * a1 * b1) % p) + p * ((a0 * b1 + a1 * b0) % p)
            self.mul = mul
        q = self.q
        self.neg = [next(b for b in range(q) if self.add(a, b) == 0) for a in range(q)]
        self.inv = [None] + [next(b for b in range(1, q) if self.mul(a, b) == 1) for a in range(1, q)]
        self.squares = sorted({self.mul(a, a) for a in range(1, q)})
        self.prim = next(g for g in range(2, q) if len({self.pw(g, i) for i in range(q - 1)}) == q - 1)

    def pw(self, a, k):
        r = 1
        for _ in range(k): r = self.mul(r, a)
        return r


def cyclic(n):
    g = tuple((x + 1) % n for x in range(n))
    return [g], closure([g], n)


def agl1(p):
    F = GF(p)
    gens = [tuple((x + 1) % p for x in range(p)), tuple(F.mul(F.prim, x) for x in range(p))]
    G = closure(gens, p); assert len(G) == p * (p - 1); return gens, G


def agl2(p):
    pts = [(a, b) for a in range(p) for b in range(p)]; idx = {v: i for i, v in enumerate(pts)}
    def perm(f): return tuple(idx[f(v)] for v in pts)
    gens = [perm(lambda v: ((v[0] + 1) % p, v[1])),
            perm(lambda v: ((v[0] + v[1]) % p, v[1])),          # transvection
            perm(lambda v: (v[1], v[0])),                          # swap (det -1)
            perm(lambda v: ((2 * v[0]) % p, v[1]))]                # diag(2,1), 2 primitive mod 5
    G = closure(gens, p * p)
    o = p * p * (p * p - 1) * (p * p - p); assert len(G) == o, (len(G), o); return gens, G


def proj_points(F, dim):
    q = F.q; pts = []
    for v in itertools.product(range(q), repeat=dim):
        if any(v):
            # normalise: first nonzero coordinate = 1
            i = next(j for j in range(dim) if v[j]); s = F.inv[v[i]]
            w = tuple(F.mul(s, a) for a in v)
            if w not in pts: pts.append(w)
    return pts


def mat_perm(F, M, pts):
    dim = len(pts[0]); idx = {}
    for i, v in enumerate(pts): idx[v] = i
    def norm(v):
        i = next(j for j in range(dim) if v[j]); s = F.inv[v[i]]
        return tuple(F.mul(s, a) for a in v)
    out = []
    for v in pts:
        w = []
        for r in range(dim):
            acc = 0
            for cc in range(dim): acc = F.add(acc, F.mul(M[r][cc], v[cc]))
            w.append(acc)
        out.append(idx[norm(tuple(w))])
    return tuple(out)


def psl3_4():
    F = GF(2, 2, nonres=None) if False else None
    # F_4 = F_2[t]/(t^2+t+1): elements a0 + 2 a1
    class F4:
        q = 4
        @staticmethod
        def add(a, b): return a ^ b
        @staticmethod
        def mul(a, b):
            a0, a1, b0, b1 = a & 1, a >> 1, b & 1, b >> 1
            # (a0 + a1 t)(b0 + b1 t) = a0b0 + (a0b1 + a1b0) t + a1b1 t^2,  t^2 = t + 1
            c0 = (a0 & b0) ^ (a1 & b1); c1 = (a0 & b1) ^ (a1 & b0) ^ (a1 & b1)
            return c0 | (c1 << 1)
    F4.inv = [None] + [next(b for b in range(1, 4) if F4.mul(a, b) == 1) for a in range(1, 4)]
    pts = proj_points(F4, 3); assert len(pts) == 21
    gens = []
    for i in range(3):
        for j in range(3):
            if i != j:
                for a in (1, 2):
                    M = [[1 if r == cc else 0 for cc in range(3)] for r in range(3)]; M[i][j] = a
                    gens.append(mat_perm(F4, M, pts))
    G = closure(gens, 21); assert len(G) == 20160, len(G)
    lines = []
    for v in pts:  # lines = points of the dual: {x : v.x = 0}
        L = tuple(sorted(i for i, x in enumerate(pts) if (F4.mul(v[0], x[0]) ^ F4.mul(v[1], x[1]) ^ F4.mul(v[2], x[2])) == 0))
        if L not in lines: lines.append(L)
    assert len(lines) == 21 and all(len(L) == 5 for L in lines)
    return gens, G, pts, lines


def psl2(p, e=1, nonres=None):
    F = GF(p, e, nonres); q = F.q; INF = q; n = q + 1
    def mob(a, b, c, d):  # z -> (a z + b) / (c z + d)
        out = []
        for z in range(n):
            if z == INF:
                out.append(INF if c == 0 else F.mul(a, F.inv[c]))
            else:
                num = F.add(F.mul(a, z), b); den = F.add(F.mul(c, z), d)
                out.append(INF if den == 0 else F.mul(num, F.inv[den]))
        return tuple(out)
    s = F.mul(F.prim, F.prim)  # a generator of the squares
    gens = [mob(1, 1, 0, 1), mob(s, 0, 0, 1), mob(0, F.neg[1], 1, 0)]
    G = closure(gens, n); o = q * (q * q - 1) // 2; assert len(G) == o, (len(G), o)
    return gens, G


if __name__ == "__main__":
    print("AGL(1,19)", len(agl1(19)[1]))
    print("AGL(2,5)", len(agl2(5)[1]))
    print("PSL(3,4)", len(psl3_4()[1]))
    print("PSL(2,25)", len(psl2(5, 2, 2)[1]))
    print("PSL(2,31)", len(psl2(31)[1]))
