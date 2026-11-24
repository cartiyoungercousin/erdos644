"""Independent checks for PETAL Theorem K (and L).  Written from the statements only.

(1) exact brute-force of the 3-round centre game on a triple-free four-petal configuration,
    integers: cells c_12,c_34 | c_13,c_24 | c_14,c_23 ; reply size k, request size <= T.
    state = multiset of (grid, side, killmask); she requests counts per class, adversary
    answers maximal subsets of the unrequested points (monotone, P3(i)); final test = P2.
(2) integer design feasibility (Theorem K(i)): types per point, cross-intersecting per grid, loads<=T.
Compare (1) and (2):  (ii) predicts equality when sigma <= k+T ; (i) predicts game>=design always.
"""
import sys, itertools, functools, random
TYPES = range(1, 8)

def comps(total, caps):
    """all vectors v, 0<=v_i<=caps_i, sum v = total"""
    if not caps:
        if total == 0: yield ()
        return
    for x in range(min(total, caps[0]) + 1):
        for rest in comps(total - x, caps[1:]):
            yield (x,) + rest

def comps_le(total, caps):
    """all vectors with sum <= total"""
    if not caps:
        yield (); return
    for x in range(min(total, caps[0]) + 1):
        for rest in comps_le(total - x, caps[1:]):
            yield (x,) + rest

# ---------- (1) brute force game ----------
def final_ok(state):
    # state: tuple of ((grid, side, mask), count)
    by = {}
    for (g, s, m), c in state:
        by.setdefault((g, s), []).append(m)
    for g in range(3):
        for x in by.get((g, 0), []):
            for y in by.get((g, 1), []):
                if x & y == 0: return False
    return True

@functools.lru_cache(maxsize=None)
def wins(state, rnd, k, T):
    if rnd == 3: return final_ok(state)
    classes = [c for c in state]
    caps = [cnt for (_, cnt) in classes]
    # prune: nothing to do if no edges remain? keep simple
    for req in comps_le(T, caps):
        # adversary answers
        rem = [caps[i] - req[i] for i in range(len(classes))]
        tot = sum(rem)
        take = min(k, tot)
        ok = True
        for rep in comps(take, rem):
            new = {}
            for i, ((g, s, m), cnt) in enumerate(classes):
                inrep = rep[i]; killed = cnt - inrep
                if inrep: new[(g, s, m)] = new.get((g, s, m), 0) + inrep
                if killed: new[(g, s, m | (1 << rnd))] = new.get((g, s, m | (1 << rnd)), 0) + killed
            st = tuple(sorted(new.items()))
            if not wins(st, rnd + 1, k, T):
                ok = False; break
        if ok: return True
    return False

def game(a, b, k, T):
    st = []
    for g in range(3):
        if a[g]: st.append(((g, 0, 0), a[g]))
        if b[g]: st.append(((g, 1, 0), b[g]))
    return wins(tuple(sorted(st)), 0, k, T)

# ---------- (2) integer design ----------
def grid_loads(a, b):
    """set of Pareto-minimal load vectors (3 rounds) of integer designs on one grid"""
    res = set()
    if a == 0 or b == 0:
        return {(0, 0, 0)}  # truly empty cell: no edge on this grid
    for ca in comps(a, [a] * 7):
        usedF = [F for F, n in zip(TYPES, ca) if n]
        for cb in comps(b, [b] * 7):
            usedG = [G for G, n in zip(TYPES, cb) if n]
            if any(F & G == 0 for F in usedF for G in usedG): continue
            ld = [0, 0, 0]
            for F, n in zip(TYPES, ca):
                for i in range(3):
                    if F >> i & 1: ld[i] += n
            for G, n in zip(TYPES, cb):
                for i in range(3):
                    if G >> i & 1: ld[i] += n
            res.add(tuple(ld))
    # pareto minimal
    res = [r for r in res if not any(o != r and all(o[i] <= r[i] for i in range(3)) for o in res)]
    return set(res)

@functools.lru_cache(maxsize=None)
def gl(a, b): return grid_loads(a, b)

def design_min(a, b):
    best = None
    for l0 in gl(a[0], b[0]):
        for l1 in gl(a[1], b[1]):
            for l2 in gl(a[2], b[2]):
                v = max(l0[i] + l1[i] + l2[i] for i in range(3))
                if best is None or v < best: best = v
    return best

if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "cmp":
        k, T, smax, cmax = map(int, sys.argv[2:6])
        rnd = random.Random(int(sys.argv[6]) if len(sys.argv) > 6 else 1)
        zero_ok = len(sys.argv) > 7 and sys.argv[7] == "zero"
        seen = 0; bad = 0; cnt = {}
        shapes = []
        lo = 0 if zero_ok else 1
        for a in itertools.product(range(lo, cmax + 1), repeat=3):
            for b in itertools.product(range(lo, cmax + 1), repeat=3):
                s = sum(a) + sum(b)
                if s <= smax and s > 0:
                    # symmetry: sort grids
                    key = tuple(sorted((min(x, y), max(x, y)) for x, y in zip(a, b)))
                    shapes.append(key)
        shapes = sorted(set(shapes))
        print("k=%d T=%d : %d shapes" % (k, T, len(shapes)), flush=True)
        for key in shapes:
            a = tuple(x for x, y in key); b = tuple(y for x, y in key)
            sigma = sum(a) + sum(b)
            dm = design_min(a, b)
            dw = dm <= T
            gw = game(a, b, k, T)
            seen += 1
            ck = (sigma <= k + T, dw, gw); cnt[ck] = cnt.get(ck, 0) + 1
            flag = ""
            if dw and not gw: flag = "SUFFICIENCY-FAIL"
            if sigma <= k + T and gw != dw: flag = "NECESSITY-FAIL (sigma<=k+T)"
            if flag:
                bad += 1
                print(flag, "cells a=%s b=%s sigma=%d designmin=%d game=%s" % (a, b, sigma, dm, gw), flush=True)
        print("done: %d shapes, %d violations" % (seen, bad)); print("stats (sigma<=k+T, designwin, gamewin): count", sorted(cnt.items()))
