"""7INV, part 1: complexity of the Fano system and the structure of the colouring measure.

(a) Cauchy-Schwarz complexity of the 7 forms L_u(y) = sum_i u_i y_i, u in F_2^3 \\ 0 (brute force over partitions).
(b) True-complexity lower bound: sum_u q(u.y) = 0 (mod 2) for every quadratic q, and sum_u |u.y| = 0 (mod 4);
    fails for some cubic q.  Dense example A = {q = 1} in F_2^10: density, max Fourier coefficient, sampled
    PG(2,2) count (expected 0) versus the independence prediction.
(c) Abelian embeddings of the per-point law mu of (1[x in R_u])_u under colourings: mu = uniform on the 7 nonzero
    codewords of the [7,3] simplex code (no zero class), or on all 8 (zero class allowed, iid uniform chi).
    E_m = { g in Z_m^7 : sum_u g_u c_u is constant on supp mu }.
Usage: py -3.14 complexity.py
"""
import itertools
import numpy as np

U = list(range(1, 8))                       # forms, as bitmasks over (y1,y2,y3)


def span(vs):
    S = {0}
    for v in vs:
        S |= {s ^ v for s in S}
    return S


def partitions(xs):
    if not xs:
        yield []
        return
    a, rest = xs[0], xs[1:]
    for p in partitions(rest):
        for i in range(len(p)):
            yield p[:i] + [[a] + p[i]] + p[i + 1:]
        yield [[a]] + p


def cs_complexity():
    out = {}
    for f in U:
        others = [g for g in U if g != f]
        best = min(len(p) for p in partitions(others) if all(f not in span(c) for c in p))
        out[f] = best - 1
    return out


def popc(x):
    return bin(x).count('1')


def test_identities(rng, n=10, trials=20000):
    bad_q, bad4, bad_cubic = 0, 0, 0
    for _ in range(trials):
        A = np.triu(rng.integers(0, 2, (n, n)), 1)
        b = rng.integers(0, 2, n)
        C = rng.integers(0, 2, (n, n, n)) * (rng.random((n, n, n)) < 0.05)
        y = rng.integers(0, 2, (3, n))
        s, s4, sc = 0, 0, 0
        for u in U:
            x = (u & 1) * y[0] ^ ((u >> 1) & 1) * y[1] ^ ((u >> 2) & 1) * y[2]
            s ^= int(x @ A @ x + b @ x) & 1
            s4 += int(x.sum())
            sc ^= int(np.einsum('ijk,i,j,k->', C, x, x, x)) & 1
        bad_q += s
        bad4 += (s4 % 4 != 0)
        bad_cubic += sc
    return bad_q, bad4, bad_cubic


def dense_quadratic(rng, n=10, samples=400000):
    xs = np.arange(1 << n)
    bits = (xs[:, None] >> np.arange(n)) & 1
    q = np.zeros(1 << n, dtype=np.int64)
    for i in range(0, n, 2):
        q ^= bits[:, i] & bits[:, i + 1]
    A = q.astype(bool)
    f = A.astype(float)
    H = f.copy()
    h = 1
    while h < len(H):                        # Walsh-Hadamard
        H = H.reshape(-1, 2, h)
        H = np.concatenate([H[:, 0] + H[:, 1], H[:, 0] - H[:, 1]], axis=1).reshape(-1)
        h *= 2
    H /= len(H)
    dens = f.mean()
    maxc = np.abs(H[1:]).max()
    y = rng.integers(0, 1 << n, (samples, 3))
    ok = np.ones(samples, dtype=bool)
    for u in U:
        v = np.zeros(samples, dtype=np.int64)
        for i in range(3):
            if u >> i & 1:
                v ^= y[:, i]
        ok &= A[v]
    return dens, maxc, int(ok.sum()), samples * dens ** 7


def embeddings():
    code = [[(popc(c & u) & 1) for u in U] for c in range(8)]   # codeword of colour c
    nz = np.array(code[1:])
    al = np.array(code)
    res = []
    for m in range(2, 9):
        G = np.array(list(itertools.product(range(m), repeat=7)))
        v_nz = (G @ nz.T) % m
        v_al = (G @ al.T) % m
        e_nz = int((v_nz == v_nz[:, :1]).all(axis=1).sum())
        e_al = int((v_al == v_al[:, :1]).all(axis=1).sum())
        # "explained": a*1 + (m/2)*h, h in Hamming code (dual of simplex), plus Hamming-type for m = 2
        ham = [h for h in itertools.product(range(2), repeat=7) if all(sum(a * b for a, b in zip(h, c)) % 2 == 0
                                                                       for c in code)]
        expl = set()
        for a in range(m):
            for h in ham:
                g = tuple((a + (m // 2) * hh) % m for hh in h) if m % 2 == 0 else tuple([a] * 7)
                expl.add(g)
        res.append((m, e_nz, e_al, len(expl), len(ham)))
    return res


def main():
    rng = np.random.default_rng(1)
    print('(a) Cauchy-Schwarz complexity per form:', cs_complexity())
    bq, b4, bc = test_identities(rng)
    print('(b) 20000 random (q, y) in F_2^10: violations of sum_u q(u.y)=0 (quadratic): %d;'
          ' of sum_u |u.y| = 0 mod 4: %d; cubic q with sum = 1: %d' % (bq, b4, bc))
    d, mc, cnt, exp = dense_quadratic(rng)
    print('    A = {x1x2+...+x9x10 = 1} in F_2^10: density %.4f, max nontrivial |Fourier| %.4f (2^-5 = %.4f),'
          ' sampled PG(2,2) in A: %d of 400000 (independence predicts %.0f)' % (d, mc, 2 ** -5, cnt, exp))
    print('(c) Abelian embeddings of the colouring law (m, |E_m| no zero class, |E_m| zero class allowed,'
          ' |<1> + (m/2)Hamming|, |Hamming|):')
    for r in embeddings():
        print('    Z_%d: %d  %d  explained %d  (Hamming %d)' % r)


if __name__ == '__main__':
    main()
