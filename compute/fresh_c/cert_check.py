r"""Independent checker for the requester-win certificates written by anchor_select.js.

It shares NO code with the solver.  It re-implements the game from its definition and only looks up the
requester's move at each of her nodes in the certificate.

What is verified (k-uniform, requests of at most T points):
 (A) anchor selection, open game: starting from one edge, at every node she plays the certified request; for
     EVERY reply (any k points avoiding the request, fresh points allowed) the next node is again certified,
     until some three replies have empty common intersection and a pair-intersection shape listed in (B).
 (B) anchored game for every shape used in (A): three anchors of that shape; at every node she plays the
     certified request; for every reply the next node is certified; after the sixth edge the set D of points
     lying in a covering pair has at most T points (her seventh request is D).

Three hand-proved facts from FRESH_C.md are used by this checker (and stated there with proofs):
 (i)  points of equal membership type are interchangeable;
 (ii) a point that is in no covering pair of the edges so far never matters again (D_{j+1} is a subset of D_j),
      and in the anchored game fresh points are never in a covering pair;
 (iii) in the anchored game it suffices to check the adversary's replies that take as many points of D_j as
      possible (taking more points of D_j only keeps more covering pairs alive).
The reduction "open continuation = game confined to the anchors" is TWIN section 13 and is NOT re-proved here.

usage: py cert_check.py cert_kK_TT_JJ.json
"""
import sys, json, itertools

sys.setrecursionlimit(100000)


def canon(items, i):
    """items: list of (mask, count).  Lexicographically smallest sorted list of mask*64+count over all
    relabellings of the i edges, together with the permutation used."""
    best = None
    bestp = None
    for p in itertools.permutations(range(i)):
        codes = []
        for m, c in items:
            v = 0
            for b in range(i):
                if (m >> b) & 1:
                    v |= 1 << p[b]
            codes.append(v * 64 + c)
        codes.sort()
        if best is None or codes < best:
            best, bestp = codes, p
    return best, bestp


def relabel(items, p, i):
    out = []
    for m, c in items:
        v = 0
        for b in range(i):
            if (m >> b) & 1:
                v |= 1 << p[b]
        out.append((v, c))
    out.sort()
    return out


def relevant(items, full):
    present = [m for m, c in items if c > 0]
    out = []
    for m, c in items:
        if c <= 0:
            continue
        need = full & ~m
        if any((m2 & need) == need for m2 in present):
            out.append((m, c))
    return out


def vectors(caps, lo_total, hi_total):
    """all tuples v, 0 <= v_j <= caps_j, lo_total <= sum <= hi_total."""
    n = len(caps)
    out = []
    cur = [0] * n

    def rec(j, used):
        if j == n:
            if used >= lo_total:
                out.append(tuple(cur))
            return
        for v in range(min(caps[j], hi_total - used), -1, -1):
            cur[j] = v
            rec(j + 1, used + v)
        cur[j] = 0

    rec(0, 0)
    return out


class Checker:
    def __init__(self, cert):
        self.k, self.T, self.J = cert["k"], cert["T"], cert["J"]
        self.cert = cert
        self.memoA = {}
        self.memoS = {}
        self.good_shapes = set()
        self.checked_nodes = 0

    # ---------------------------------------------------------------- (B) anchored game
    def anchored(self, items, i, nodes):
        """items: relevant (mask, count) after i edges.  True iff the certificate wins from here."""
        k, T = self.k, self.T
        tot = sum(c for _, c in items)
        if tot <= T:
            return True                       # she requests D
        if i == 6:
            return False
        codes, p = canon(items, i)
        key = f"{i}:" + ",".join(map(str, codes))
        mk = (id(nodes), key)
        if mk in self.memoA:
            return self.memoA[mk]
        if key not in nodes:
            raise SystemExit(f"FAIL: anchored node not in certificate: {key}")
        st = relabel(items, p, i)
        s = nodes[key]
        if len(s) != len(st) or any(x < 0 or x > c for x, (_, c) in zip(s, st)) or sum(s) > T:
            raise SystemExit(f"FAIL: illegal request at {key}")
        self.checked_nodes += 1
        rest = [c - x for x, (_, c) in zip(s, st)]
        U = sum(rest)
        b = 1 << i
        full = (1 << (i + 1)) - 1
        replies = [tuple(rest)] if U <= k else vectors(rest, k, k)
        ok = True
        for a in replies:
            nxt = []
            for (m, c), x in zip(st, a):
                if x:
                    nxt.append((m | b, x))
                if c - x:
                    nxt.append((m, c - x))
            nxt = relevant(nxt, full)
            if not self.anchored(nxt, i + 1, nodes):
                ok = False
                break
        self.memoA[mk] = ok
        return ok

    def shape_ok(self, name):
        if name in self.memoS:
            return self.memoS[name]
        k = self.k
        if name not in self.cert["shapes"]:
            self.memoS[name] = False
            return False
        p12, p13, p23 = map(int, name.split(","))
        c1, c2, c3 = k - p12 - p13, k - p12 - p23, k - p13 - p23
        if min(c1, c2, c3) < 0:
            raise SystemExit(f"FAIL: impossible shape {name}")
        items = relevant([(3, p12), (5, p13), (6, p23), (1, c1), (2, c2), (4, c3)], 7)
        r = self.anchored(items, 3, self.cert["shapes"][name])
        self.memoS[name] = r
        return r

    # ---------------------------------------------------------------- (A) anchor selection
    def has_winning_triple(self, items, j):
        for a, b, c in itertools.combinations(range(j), 3):
            tri = pab = pac = pbc = 0
            for m, cnt in items:
                ia, ib, ic = (m >> a) & 1, (m >> b) & 1, (m >> c) & 1
                if ia and ib and ic:
                    tri += cnt
                elif ia and ib:
                    pab += cnt
                elif ia and ic:
                    pac += cnt
                elif ib and ic:
                    pbc += cnt
            if tri:
                continue
            name = ",".join(map(str, sorted([pab, pac, pbc], reverse=True)))
            if self.shape_ok(name):
                return True
        return False

    def select(self, items, j, memo):
        k, T, J = self.k, self.T, self.J
        codes, p = canon(items, j)
        key = f"{j}:" + ",".join(map(str, codes))
        if key in memo:
            return memo[key]
        if j >= 3 and self.has_winning_triple(items, j):
            memo[key] = True
            return True
        if j == J:
            memo[key] = False
            return False
        if key not in self.cert["as"]:
            raise SystemExit(f"FAIL: anchor-selection node not in certificate: {key}")
        st = relabel(items, p, j)
        s = self.cert["as"][key]
        if len(s) != len(st) or any(x < 0 or x > c for x, (_, c) in zip(s, st)) or sum(s) > T:
            raise SystemExit(f"FAIL: illegal request at {key}")
        self.checked_nodes += 1
        rest = [c - x for x, (_, c) in zip(s, st)]
        b = 1 << j
        ok = True
        for a in vectors(rest, 0, k):
            nxt = []
            for (m, c), x in zip(st, a):
                if x:
                    nxt.append((m | b, x))
                if c - x:
                    nxt.append((m, c - x))
            fresh = k - sum(a)
            if fresh:
                nxt.append((b, fresh))
            if not self.select(nxt, j + 1, memo):
                ok = False
                break
        memo[key] = ok
        return ok


if __name__ == "__main__":
    cert = json.load(open(sys.argv[1]))
    ch = Checker(cert)
    ok = ch.select([(1, cert["k"])], 1, {})
    print(f"{sys.argv[1]}: k={cert['k']} T={cert['T']} J={cert['J']} (m = {cert['J'] + 4} requests): "
          f"{'CERTIFICATE VERIFIED' if ok else 'CERTIFICATE REJECTED'}; her nodes checked: {ch.checked_nodes}; "
          f"shapes verified as wins: {sum(1 for v in ch.memoS.values() if v)}")
