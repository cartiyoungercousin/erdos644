"""Independent check of CORE 46: the ordered frozen anti-plan (two-cell rule). Rule applied verbatim; all pairs of the seven checked."""
import random, sys
from vw import plan, fano_lines, cover_ok


def rule(n, k, T, o):
    c = n - k
    u = 2 * (c - o)
    g = n - o - u
    om = n - k - T
    O = list(range(o)); U = list(range(o, o + u)); G = list(range(o + u, n))

    def reply(S):
        S = set(S)
        d = n - k - len(S)
        cell = O if len(S & set(O)) < om else U
        out = [x for x in cell if x not in S][:d]
        if len(out) < d:                       # fallback (not exercised on requests used; counted)
            reply.fallback += 1
            for x in O + U + G:
                if len(out) >= d: break
                if x not in S and x not in out: out.append(x)
        return S | set(out)
    reply.fallback = 0
    return reply, O, U, G, om, g


def attempt(n, k, T, o, rng, branch):
    reply, O, U, G, om, g = rule(n, k, T, o)
    if g < 0 or o < 2 * om or len(U) < 2 * om or om < 1:
        return 'outside_hyp'
    pl = plan(k, T)
    if pl is None:
        return 'noplan'
    dk, A, coset = pl
    kap = n - dk
    ps = [sum(a) for a in A]
    nonO = U + G
    if branch == 'L':
        U1 = U[:om]
        if 2 * om > kap: return 'notapplicable'
        Oset = O[-om:]                                  # last omega points of O (adversarial: not the head)
        kernel = set(U1) | set(Oset)
        extra = [x for x in nonO if x not in kernel]; rng.shuffle(extra)
        kernel |= set(extra[:kap - len(kernel)])
        if len(kernel) != kap: return 'notapplicable'
        head = set(U1)
        pool = [x for x in range(n) if x not in kernel]
        rng.shuffle(pool)
        pet = []; pos = 0
        for p in ps: pet.append(set(pool[pos:pos + p])); pos += p
    else:
        O1 = O[:om]
        if kap - om > len(nonO): return 'notapplicable'
        rem = o - om
        q = []
        left = rem
        for i in range(3):
            share = min(om - 1, ps[i], left - 0)
            q.append(share)
            left -= share
        # distribute evenly instead of greedily
        base = [0, 0, 0]
        left = rem
        while left > 0:
            moved = False
            for i in range(3):
                if left > 0 and base[i] < min(om - 1, ps[i]):
                    base[i] += 1; left -= 1; moved = True
            if not moved: break
        if left > 0: return 'notapplicable'
        kernel = set(O1)
        ne = nonO[:]; rng.shuffle(ne)
        kernel |= set(ne[:kap - om])
        used_nonO = set(ne[:kap - om])
        rest_nonO = [x for x in nonO if x not in used_nonO]
        rng.shuffle(rest_nonO)
        Orest = O[om:]; rng.shuffle(Orest)
        pet = []; po = 0; pn = 0
        for i in range(3):
            pts = set(Orest[po:po + base[i]]); po += base[i]
            need = ps[i] - base[i]
            pts |= set(rest_nonO[pn:pn + need]); pn += need
            pet.append(pts)
        head = set(O1)
        if pn != len(rest_nonO): return 'notapplicable'
    Ks = []
    for i in range(3):
        L = kernel | pet[i]
        assert len(L) <= n - k
        S = L - head
        assert len(S) <= T
        K = reply(S)
        if not L <= K: return 'FAIL_pencil_' + branch
        Ks.append(K)
    # classes inside petals
    cls = []
    for i in range(3):
        pts = sorted(pet[i]); rng.shuffle(pts)
        cls.append((set(pts[:A[i][0]]), set(pts[A[i][0]:])))
    for bits in fano_lines(coset):
        L = set()
        for i in range(3): L |= cls[i][bits[i]]
        assert len(L) <= T
        Ks.append(reply(L))
    ok, ts = cover_ok(n, Ks)
    return 'OK' if ok and reply.fallback == 0 else ('FAIL_cover_' + branch if not ok else 'fallback')


def main():
    rng = random.Random(7)
    tot = {}; bad = []
    for k in list(range(8, 31)) + [40]:
        for T in sorted({-(-3 * k // 4), -(-3 * k // 4) + 1, -(-3 * k // 4) + 2}):
            for n in range(k + T, int(2.3 * k) + 1, max(1, k // 20)):
                om = n - k - T
                for o in range(max(2 * om, n - 2 * k, 1), n - k - om + 1, max(1, k // 25)):
                    res = []
                    for br in ('H', 'L'):
                        res.append(attempt(n, k, T, o, rng, br))
                    if 'outside_hyp' in res:
                        key = 'outside_hyp'
                    elif 'OK' in res:
                        key = 'OK'
                    else:
                        key = 'NEITHER:' + ','.join(res)
                    tot[key] = tot.get(key, 0) + 1
                    if key.startswith('NEITHER') or 'FAIL' in str(res):
                        bad.append((k, T, n, o, om, res))
    print(tot)
    for b in bad[:40]: print(b)


if __name__ == '__main__':
    main()
