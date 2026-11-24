r"""Exact solver (no relaxation) for the 7-request game on 2k points with one fixed edge.

Ground set V, |V| = 2k; A_1 = k of the points.  For i = 2..7: the requester names a set S_i of at most T points,
the adversary answers with ANY k-subset A_i of V \ S_i.  The requester wins iff A_1..A_7 have no 2-cover
(no points x, y, possibly equal, such that every A_i contains x or y).

Exact reductions used (all proved in FRESH_C.md section 8.3 / 12):
 * cover graph: G_j = pairs {x,y} covering A_1..A_j, D_j = points in some pair.  G_{j+1} = pairs of G_j meeting
   A_{j+1}; so D_{j+1} is a subset of D_j, points outside D_j never matter again, and the game depends only on the
   membership types of the points of D_j (points of equal type are interchangeable);
 * the requester wins iff some |D_j| <= T with j <= 6 (he then requests D_j);
 * monotonicity: requesting more never hurts the requester (so |S| = T inside D_j), taking more points of D_j
   never hurts the adversary (so he takes all unrequested points of D_j if there are at most k, else k of them).
The search is a plain AND/OR search over type-count states with a transposition table keyed by the state
canonicalised under permutations of the edge labels."""
import sys, time, itertools
from functools import lru_cache

sys.setrecursionlimit(100000)


def bits(m):
    return [b for b in range(8) if (m >> b) & 1]


PERMS = {}
for i in range(1, 6):
    maps = []
    for p in itertools.permutations(range(i)):
        mp = [0] * (1 << i)
        for m in range(1 << i):
            v = 0
            for b in range(i):
                if (m >> b) & 1:
                    v |= 1 << p[b]
            mp[m] = v
        maps.append(tuple(mp))
    PERMS[i] = maps


def canon(items, i):
    """items: list of (mask, count) -> canonical tuple under edge relabelling."""
    best = None
    for mp in PERMS[i]:
        t = tuple(sorted((mp[m], c) for m, c in items))
        if best is None or t < best:
            best = t
    return best


def relevant(items, full):
    """keep the types having a partner type (J | J' == full) among the present ones."""
    masks = [m for m, c in items if c > 0]
    out = []
    for m, c in items:
        if c <= 0:
            continue
        need = full & ~m
        ok = False
        for m2 in masks:
            if (m2 & need) == need:
                ok = True
                break
        if ok:
            out.append((m, c))
    return out


def vectors(caps, total):
    """all tuples v with 0 <= v_j <= caps_j and sum = total."""
    n = len(caps)
    suffix = [0] * (n + 1)
    for j in range(n - 1, -1, -1):
        suffix[j] = suffix[j + 1] + caps[j]
    out = []
    cur = [0] * n

    def rec(j, rem):
        if j == n:
            if rem == 0:
                out.append(tuple(cur))
            return
        lo = max(0, rem - suffix[j + 1])
        hi = min(caps[j], rem)
        for v in range(hi, lo - 1, -1):
            cur[j] = v
            rec(j + 1, rem - v)
        cur[j] = 0

    rec(0, total)
    return out


class Game:
    def __init__(self, k, T):
        self.k, self.T = k, T
        self.memo = {}
        self.best = {}       # winning request at winning nodes
        self.nodes = 0
        self.fast_last = True

    def children(self, state, i, s):
        """all distinct successor states (canonical) after request s; state = tuple of (mask, count)."""
        k = self.k
        rest = [c - x for (m, c), x in zip(state, s)]
        U = sum(rest)
        b = 1 << i
        full = (1 << (i + 1)) - 1
        take = min(k, U)
        seen = set()
        res = []
        for a in ([tuple(rest)] if U <= k else vectors(rest, take)):
            items = []
            for (m, c), x in zip(state, a):
                if x:
                    items.append((m | b, x))
                if c - x:
                    items.append((m, c - x))
            items = relevant(items, full)
            tot = sum(c for _, c in items)
            if i + 1 <= 5:
                key = canon(items, i + 1)
            else:
                key = tot                      # after six edges only |D| matters
            if key in seen:
                continue
            seen.add(key)
            res.append((tot, key, a))
        res.sort(key=lambda z: -z[0] if not isinstance(z[1], int) else -z[0])
        return res

    def win(self, state, i):
        """requester to move with i edges so far; state = canonical tuple of relevant (mask, count)."""
        T = self.T
        tot = sum(c for _, c in state)
        if tot <= T:
            return True
        if i == 6:
            return False
        key = (i, state)
        if key in self.memo:
            return self.memo[key]
        self.nodes += 1
        if i == 5 and self.fast_last:
            r = self.last_round(state)
            if r is not None:
                self.memo[key] = r
                return r
        caps = [c for _, c in state]
        full = (1 << i) - 1
        # neighbour weights for ordering the requests
        w = []
        for m, c in state:
            need = full & ~m
            w.append(sum(c2 for m2, c2 in state if (m2 & need) == need))
        reqs = vectors(caps, T)
        reqs.sort(key=lambda s: -sum(x * ww for x, ww in zip(s, w)))
        result = False
        for s in reqs:
            ok = True
            for tot2, key2, a in self.children(state, i, s):
                if i + 1 == 6:
                    if tot2 > T:
                        ok = False
                        break
                else:
                    if tot2 > T and not self.win(key2, i + 1):
                        ok = False
                        break
            if ok:
                result = True
                self.best[key] = s
                break
        self.memo[key] = result
        return result

    def last_round(self, state):
        """Exact evaluation of the final request (5 edges so far) without enumerating requests and replies.
        The requester fully requests a set B of types (cost = their sizes) and spends the rest of the budget on
        points the adversary could add outside N(Theta); the adversary then touches every remaining type Theta
        (one point each is enough to keep all of N(Theta) alive) and fills his edge with further points of Theta.
        Returns None (fall back to enumeration) in the rare case that he cannot touch all of Theta."""
        k, T = self.k, self.T
        n = len(state)
        masks = [m for m, _ in state]
        cnt = [c for _, c in state]
        full = 31
        adj = [0] * n
        for a in range(n):
            need = full & ~masks[a]
            for b in range(n):
                if (masks[b] & need) == need:
                    adj[a] |= 1 << b
        best_fail = False
        for B in range(1 << n):
            cost = 0
            for j in range(n):
                if (B >> j) & 1:
                    cost += cnt[j]
            if cost > T:
                continue
            theta = ((1 << n) - 1) & ~B
            nb = 0
            for j in range(n):
                if (theta >> j) & 1:
                    nb |= adj[j]
            ntheta = bin(theta).count("1")
            if ntheta > k:
                return None
            dn = sum(cnt[j] for j in range(n) if (nb >> j) & 1)
            out_types = theta & ~nb
            t_in = bin(theta & nb).count("1")
            n_out = bin(out_types).count("1")
            u_out = sum(cnt[j] for j in range(n) if (out_types >> j) & 1)
            u_left = max(n_out, u_out - (T - cost))
            d6 = dn + min(k - t_in, u_left)
            if d6 <= T:
                self.best[(5, state)] = ("block", tuple(masks[j] for j in range(n) if (B >> j) & 1))
                return True
        return False

    def root(self):
        k = self.k
        items = relevant([(1, k), (0, k)], 1)
        return canon(items, 1)

    def solve(self):
        return self.win(self.root(), 1)

    def main_line(self):
        """play the stored winning requests against the adversary reply leaving the largest D."""
        lines = []
        state, i = self.root(), 1
        while True:
            tot = sum(c for _, c in state)
            if tot <= self.T or i == 6:
                lines.append(f"  after {i} edges: |D| = {tot}  types {fmt(state)}  -> requester requests D and wins" if tot <= self.T else f"  after {i} edges: |D| = {tot}")
                break
            s = self.best.get((i, state))
            if isinstance(s, tuple) and len(s) == 2 and s[0] == "block":
                lines.append(f"  after {i} edges: |D| = {tot}  types {fmt(state)}  final request: all points of types "
                             + ", ".join("".join(str(b + 1) for b in bits(m)) for m in s[1]) + " (+ spare budget on addable points) -> |D_6| <= T")
                break
            if s is None:
                lines.append("  (no stored move)")
                break
            ch = self.children(state, i, s)
            lines.append(f"  after {i} edges: |D| = {tot}  types {fmt(state)}  request {fmt(tuple((m, x) for (m, c), x in zip(state, s) if x))}")
            tot2, key2, a = ch[0]
            if i + 1 == 6:
                lines.append(f"  after 6 edges (adversary's best reply): |D| = {tot2}")
                break
            state, i = key2, i + 1
        return lines


def fmt(state):
    return "{" + ", ".join(("".join(str(b + 1) for b in bits(m)) or "-") + f":{c}" for m, c in state) + "}"


if __name__ == "__main__":
    k = int(sys.argv[1])
    Ts = [int(x) for x in sys.argv[2:]] or list(range(-(-3 * k // 4), k))
    for T in Ts:
        t0 = time.time()
        g = Game(k, T)
        r = g.solve()
        print(f"k={k} T={T} (T/k={T / k:.4f}): {'REQUESTER wins' if r else 'ADVERSARY wins'}   states={len(g.memo)}  [{time.time() - t0:.1f}s]", flush=True)
        if r:
            for ln in g.main_line():
                print(ln, flush=True)
