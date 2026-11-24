"""PETAL Part III, Theorem N check [simulation, not a proof].
Adversary: two disjoint arenas of n = k + T/2 - d points; a reply of colour c has k-d-(extra) points in its own arena, chosen
to MAXIMISE the minimum overlap with all earlier replies of colour c (ILP on atoms; at least the value of the uniform rule), and
>= d points in the other arena; it contains one point of every earlier pair-intersection not fully requested (slivers).
Requester: randomised targeted lines (colour forcing with shaped complements; sealing a same-colour pair and the bands of up to
3 opposite replies, remainder aimed at the served replies).  After each reply every quadruple of replies is tested: triple-free?
then the max over grids of L* (lower bound for the design value) is compared with T; if it is <= T+1 the full design MILP is run.
usage: py sim_arena.py k T d games [seed]
"""
import sys, random, itertools
from lpw import Model, esum
from lstar import lstar
from quadmin import add_design


def run(k, T, d, games, seed=1, maxreq=9):
    rnd = random.Random(seed)
    n = k + T // 2 - d
    VA = set(range(n)); VF = set(range(n, 2 * n)); ARENA = {"A": VA, "F": VF}; OTHER = {"A": "F", "F": "A"}
    stats = dict(games=0, replies=0, quads=0, triplefree=0, minmargin=1e9, good=0, sealed_moves=0, worst=None)

    def adversary(S, reps):
        xa = len(S & VA); xf = len(S & VF)
        if xa * 2 > T: c = "F"
        elif xf * 2 > T: c = "A"
        else: c = rnd.choice("AF")
        own = ARENA[c] - S; oth = ARENA[OTHER[c]] - S
        targets = []
        for (u, cu), (v, cv) in itertools.combinations(reps, 2):
            w = (u & v) - S
            if w: targets.append(w)
        sl = set()
        while True:
            rem = [w for w in targets if not (w & sl)]
            if not rem: break
            cnt = {}
            for w in rem:
                for x in w: cnt[x] = cnt.get(x, 0) + 1
            best = max(sorted(cnt), key=lambda x: (cnt[x], x in own)); sl.add(best)
        sl_own = sl & own; sl_oth = sl - own
        band = set(sl_oth)
        pool = sorted(oth - band); rnd.shuffle(pool)
        while len(band) < d: band.add(pool.pop())
        m_own = k - len(band)
        same = [u for (u, cu) in reps if cu == c]
        atoms = {}
        for x in sorted(own):
            key = tuple(x in u for u in same); atoms.setdefault(key, []).append(x)
        keys = list(atoms)
        M = Model(); z = M.var(0, k)
        xs = {}
        for key in keys:
            lb = sum(1 for x in atoms[key] if x in sl_own)
            xs[key] = M.var(lb, len(atoms[key]), True)
        M.eq(esum(xs.values()), m_own)
        for i in range(len(same)):
            M.le(z, esum(xs[key] for key in keys if key[i]))
        st, val = M.minimize(-1 * z)
        E = set(band)
        for key in keys:
            cnt = int(round(M.val(xs[key])))
            must = [x for x in atoms[key] if x in sl_own]; rest = [x for x in atoms[key] if x not in sl_own]; rnd.shuffle(rest)
            E.update(must); E.update(rest[:cnt - len(must)])
        assert len(E) == k and not (E & S), (len(E), st)
        return E, c

    def take(pref_lists, m, forbid):
        out = set()
        for lst in pref_lists:
            lst = sorted(x for x in set(lst) if x not in forbid and x not in out); rnd.shuffle(lst)
            out.update(lst[:m - len(out)])
            if len(out) == m: break
        return out

    def force_move(reps):
        c = rnd.choice("AF"); o = OTHER[c]
        same = [u for (u, cu) in reps if cu == c]; opp = [u for (u, cu) in reps if cu != c]
        S = set()
        pref = []
        cross = set()
        if same and opp and rnd.random() < 0.8:          # seal cross-colour pair-intersections: makes (X, Y, new) triples slivers-free
            for u in same:
                for v in opp: cross |= (u & v)
            pref.append([x for x in cross if x in ARENA[o]])
        if same: pref.append([x for u in same for x in u if x in ARENA[o]])
        if opp and rnd.random() < 0.5: pref.append(list(rnd.choice(opp) & ARENA[o]))
        pref.append(list(ARENA[o]))
        S |= take(pref, T // 2 + 1, S)
        pref = [[x for x in cross if x in ARENA[c]]]
        mode = rnd.randrange(4)
        if same and mode == 0: pref.append(list(rnd.choice(same) & ARENA[c]))
        if same and mode == 1:
            I = set(ARENA[c])
            for u in same: I &= u
            pref.append(list(I))
        if len(same) >= 2 and mode == 2:
            u, v = rnd.sample(same, 2); pref.append(list(u & v))
        pref.append(list(ARENA[c]))
        S |= take(pref, T - len(S), S)
        return S

    def seal_move(reps):
        c = rnd.choice("AF"); o = OTHER[c]
        same = [u for (u, cu) in reps if cu == c]; opp = [u for (u, cu) in reps if cu != c]
        if len(same) < 2 or not opp: return None
        if rnd.random() < 0.7: i, j = min(itertools.combinations(range(len(same)), 2), key=lambda p: len(same[p[0]] & same[p[1]]))
        else: i, j = rnd.sample(range(len(same)), 2)
        X, X2 = same[i], same[j]
        S = set(X & X2)
        ys = rnd.sample(opp, min(len(opp), rnd.choice([1, 1, 2, 3])))
        served = []
        for Y in ys:
            add = (Y & (X | X2)) - S
            if len(S) + len(add) <= T: S |= add; served.append(Y)
        if len(S) > T or not served: return None
        mode = rnd.randrange(4); pref = []
        I = set(ARENA[o])
        for Y in served: I &= Y
        if mode == 0: pref.append(list(I))
        if mode == 1: pref.append(list(rnd.choice(served) & ARENA[o]))
        if mode == 2:
            for Y in served: pref.append(list(Y & ARENA[o]))
        if mode == 3: pref.append([x for Y in served for x in Y if x in ARENA[o] and x not in I])
        pref.append(list(ARENA[o])); pref.append(list(ARENA[c]))
        S |= take(pref, T - len(S), S)
        stats["sealed_moves"] += 1
        return S

    def check(reps):
        new = len(reps) - 1
        for tri in itertools.combinations(range(new), 3):
            q = list(tri) + [new]; sets = [reps[i][0] for i in q]
            stats["quads"] += 1
            U = set().union(*sets)
            cells = {p: 0 for p in itertools.combinations(range(4), 2)}; ok = True
            for x in U:
                J = tuple(i for i in range(4) if x in sets[i])
                if len(J) >= 3: ok = False; break
                if len(J) == 2: cells[J] += 1
            if not ok: continue
            stats["triplefree"] += 1
            grids = [((0, 1), (2, 3)), ((0, 2), (1, 3)), ((0, 3), (1, 2))]
            lb = max(lstar(cells[g[0]], cells[g[1]]) for g in grids)
            val = lb
            if lb <= T + 1:
                M = Model(); L = M.var()
                add_design(M, {p: float(v) for p, v in cells.items()}, L); st, val = M.minimize(L)   # exact zero cells: favours her
            if val - T < stats["minmargin"]:
                stats["minmargin"] = val - T; stats["worst"] = (dict(cells), [reps[i][1] for i in q], round(val, 2))
            if val <= T: stats["good"] += 1

    for g in range(games):
        reps = []
        stats["games"] += 1
        for r in range(maxreq):
            S = None
            if len(reps) >= 3 and rnd.random() < 0.6: S = seal_move(reps)
            if S is None: S = force_move(reps)
            E, c = adversary(S, reps); reps.append((E, c)); stats["replies"] += 1
            check(reps)
    return stats


if __name__ == "__main__":
    k, T, d, games = map(int, sys.argv[1:5]); seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    s = run(k, T, d, games, seed)
    from lstar import a0, beta
    t = T / k; dl = d / k
    print("k=%d T=%d d=%d (delta=%.4f): theory a0=%.1f beta=%.1f L*(a0,beta)-T=%.2f | %s" %
          (k, T, d, dl, a0(t, dl) * k, beta(t, dl) * k, (lstar(a0(t, dl), beta(t, dl)) - t) * k, s))
