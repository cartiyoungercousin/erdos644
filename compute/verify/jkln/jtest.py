"""Independent test of PETAL Theorem J (section 3).  Written from the statement/proof only.

Integer model (k points per reply, requests <= T points, replies disjoint from the request).
  same class  : overlap >= C+1            (i.e. > c k)
  different   : overlap <= Lm-1           (i.e. < lambda k)
  band        : Lm <= overlap <= C        -> if it ever occurs the requester has met disjunct 2 and the game stops.
The requester follows exactly the proof: Step 1 (b-requests on running intersections of the two classes + standing
request X1 n Y1), Step 2 (three forcing requests), Theorem D when a third class appears.
The adversary is *any legal* sequence: every reply is the solution of a small ILP over Venn cells (all earlier
replies' signatures) enforcing the class constraints for a chosen class, with several objectives
(keep/avoid the running intersection, maximise trace on U, random).  If no class is feasible the adversary is
forced into the band.  Final check: the seven replies used have no 2-cover (exact).
Budget assertions: every request has size <= T (checked, never clipped)."""
import sys, random, itertools
import numpy as np
import highspy
inf = highspy.kHighsInf


def cover_ok(sets):
    """True iff NO 2-cover exists (two points hitting all sets)."""
    pts = set().union(*sets)
    mask = {}
    for j, s in enumerate(sets):
        for x in s: mask[x] = mask.get(x, 0) | (1 << j)
    ms = sorted(set(mask.values())); full = (1 << len(sets)) - 1
    for i in range(len(ms)):
        for j in range(i, len(ms)):
            if ms[i] | ms[j] == full: return False
    return True


class Sim:
    def __init__(self, k, T, C, Lm, rnd, policy):
        self.k, self.T, self.C, self.Lm, self.rnd, self.policy = k, T, C, Lm, rnd, policy
        self.reps = []            # list of frozenset
        self.nextid = 0
        self.reqs = []
        self.stuck = False

    def cls(self):
        """classes by overlap > C (assert equivalence + no band)."""
        n = len(self.reps); lab = list(range(n))
        for i in range(n):
            for j in range(i):
                o = len(self.reps[i] & self.reps[j])
                if self.Lm <= o <= self.C: return None   # band
        for i in range(n):
            for j in range(i):
                if len(self.reps[i] & self.reps[j]) > self.C: lab[i] = lab[j]; break
        # check transitivity
        for i in range(n):
            for j in range(i):
                same = len(self.reps[i] & self.reps[j]) > self.C
                assert same == (lab[i] == lab[j]), "not an equivalence relation?!"
        groups = {}
        for i in range(n): groups.setdefault(lab[i], []).append(i)
        return sorted(groups.values(), key=lambda g: g[0])

    # ----- adversary -----
    def reply(self, S, tag=""):
        S = set(S); self.reqs.append(S)
        k, rnd = self.k, self.rnd
        classes = self.cls()
        assert classes is not None
        # cells by signature, excluding S
        pts = set().union(*self.reps) if self.reps else set()
        cells = {}
        for p in pts:
            if p in S: continue
            sig = tuple(i for i, r in enumerate(self.reps) if p in r)
            cells.setdefault(sig, []).append(p)
        cell_list = list(cells.items()) + [((), None)]            # last: fresh points
        cand = [("join", ci) for ci in range(len(classes))] + [("new", None)]
        rnd.shuffle(cand)
        pol = self.policy
        if pol == "new":    cand.sort(key=lambda c: 0 if c[0] == "new" else 1)
        if pol == "big":    cand.sort(key=lambda c: -len(classes[c[1]]) if c[0] == "join" else 1)
        if pol == "small":  cand.sort(key=lambda c: len(classes[c[1]]) if c[0] == "join" else 99)
        import os
        obj = os.environ.get("JOBJ") or rnd.choice(["keepI", "avoidI", "rand", "traceU", "maxold", "minold"])
        for kind, ci in cand:
            res = self._try(cell_list, classes, kind, ci, obj, S)
            if res is not None:
                self.reps.append(frozenset(res)); return len(self.reps) - 1
        self.stuck = True
        return None

    def _try(self, cell_list, classes, kind, ci, obj, S):
        k, C, Lm, rnd = self.k, self.C, self.Lm, self.rnd
        h = highspy.Highs(); h.setOptionValue("output_flag", False)
        nv = len(cell_list)
        same = set(classes[ci]) if kind == "join" else set()
        # running intersection of first 4 members of the target class
        I = None
        if kind == "join":
            I = set(self.reps[classes[ci][0]])
            for m in classes[ci][1:4]: I &= self.reps[m]
        # union U of first 4 members of the biggest class
        big = max(classes, key=len) if classes else []
        U = set()
        for m in big[:4]: U |= self.reps[m]
        cost = []
        for sig, pl in cell_list:
            size = len(pl) if pl is not None else k
            w = 0.0
            if pl is not None:
                rep0 = pl[0]
                if obj == "keepI" and I is not None and rep0 in I: w = 1
                if obj == "avoidI" and I is not None and rep0 in I: w = -1
                if obj == "traceU" and rep0 in U: w = 1
                if obj == "maxold": w = len(sig)
                if obj == "minold": w = -len(sig)
                if obj == "rand": w = rnd.random()
            else:
                if obj == "rand": w = rnd.random()
            cost.append(w)
        for j, (sig, pl) in enumerate(cell_list):
            size = len(pl) if pl is not None else k
            h.addVar(0, size); h.changeColCost(j, -cost[j] - 1e-3 * rnd.random())   # minimise -w
            h.changeColIntegrality(j, highspy.HighsVarType.kInteger)
        h.addRow(k, k, nv, list(range(nv)), [1.0] * nv)
        for m in range(len(self.reps)):
            idx = [j for j, (sig, pl) in enumerate(cell_list) if m in sig]
            if not idx:
                if m in same: return None
                continue
            if m in same: h.addRow(C + 1, k, len(idx), idx, [1.0] * len(idx))
            else:         h.addRow(0, Lm - 1, len(idx), idx, [1.0] * len(idx))
        h.run()
        if h.getModelStatus() != highspy.HighsModelStatus.kOptimal: return None
        x = [int(round(v)) for v in h.getSolution().col_value]
        out = []
        for (sig, pl), cnt in zip(cell_list, x):
            if pl is None:
                for _ in range(cnt): out.append(self.nextid); self.nextid += 1
            else:
                out += rnd.sample(pl, cnt)
        # fresh ids for first reply when no points exist handled via fresh cell
        return out


def pick(rnd, pool, n):
    pool = list(pool)
    return set(rnd.sample(pool, min(n, len(pool))))


def play(k, T, C, Lm, seed, policy, verbose=False):
    rnd = random.Random(seed)
    sm = Sim(k, T, C, Lm, rnd, policy)
    b = (T - (Lm - 1)) // 2
    assert k - 2 * b <= b, "param: 1-2b<=b fails"
    info = {"outcome": None, "maxreq": 0, "step2": False, "D": False}

    def done_band(): info["outcome"] = "band"; return info

    # ---- Step 1 ----
    classes = []
    for step in range(7):
        classes = sm.cls()
        S = set()
        for g in classes:
            I = set(sm.reps[g[0]])
            for m in g[1:4]: I &= sm.reps[m]
            S |= pick(rnd, I, b) if len(I) > b else set(I)
        if len(classes) >= 2:
            X1, Y1 = sm.reps[classes[0][0]], sm.reps[classes[1][0]]
            S |= (X1 & Y1)
        assert len(S) <= T, ("step1 request too big", len(S), T)
        info["m1"] = max(info.get("m1", 0), len(S))
        r = sm.reply(S)
        if r is None: return done_band() if True else info
        classes = sm.cls()
        if classes is None: return done_band()
        if len(classes) >= 3:
            return finishD(sm, classes, info, k, T, rnd)
        if any(len(g) >= 4 for g in classes): break
    classes = sm.cls()
    big = [g for g in classes if len(g) >= 4]
    assert big, "pigeonhole failed: no class with 4 members after 7 replies"
    X = big[0][:4]
    U = set().union(*[sm.reps[m] for m in X])
    I4 = set(sm.reps[X[0]])
    for m in X[1:]: I4 &= sm.reps[m]
    assert not I4, "four class members have nonempty common intersection"
    info["step2"] = True
    X1 = sm.reps[X[0]]
    cent = []; Z = []
    for j in range(3):
        classes = sm.cls()
        Zprev = set().union(*Z) if Z else set()
        Fneed = Zprev & X1
        F = set(Fneed)
        assert len(Fneed) <= k - C, ("F cannot contain traces", len(Fneed), k - C)
        F |= pick(rnd, X1 - F, k - C - len(F))
        S = F | (Zprev - X1)
        # standing request
        cl_other = [g for g in classes if g != big[0] and X[0] not in g]
        if cl_other:
            S |= (X1 & sm.reps[cl_other[0][0]])
        assert len(S) <= T, ("step2 request too big", j, len(S), T)
        info["m2"] = max(info.get("m2", 0), len(S))
        r = sm.reply(S)
        if r is None: return done_band()
        cent.append(r); Z.append(set(sm.reps[r]) & U)
        classes = sm.cls()
        if classes is None: return done_band()
        if len(classes) >= 3 and r is not None:
            # is the newest reply in a class other than X's and the other class?
            lab = [g for g in classes if r in g][0]
            if lab[0] == r and len(classes) >= 3 and len(lab) == 1:
                return finishD(sm, classes, info, k, T, rnd)
    # final check
    for i in range(3):
        for j in range(i):
            assert not (Z[i] & Z[j]), "traces not disjoint"
    seven = [sm.reps[m] for m in X] + [sm.reps[m] for m in cent]
    ok = cover_ok(seven)
    info["outcome"] = "win7" if ok else "FAIL-COVER"
    info["maxreq"] = len(sm.reqs)
    return info


def finishD(sm, classes, info, k, T, rnd):
    """Theorem D on anchors = first members of three classes (the third class's first member just arrived)."""
    info["D"] = True
    a1, a2, a3 = [g[0] for g in classes[:3]]
    A = [sm.reps[a1], sm.reps[a2], sm.reps[a3]]
    # D requires empty triple intersection; (standing request guarantees it)
    triple = A[0] & A[1] & A[2]
    assert not triple, "anchors have common point (standing-request argument fails)"
    P = (A[0] & A[1]) | (A[0] & A[2]) | (A[1] & A[2])
    p = len(P)
    assert p < 3 * sm.Lm, ("pair mass not < 3 lambda", p)
    assert 3 * p <= 3 * T - k, ("Theorem D budget p <= T - k/3 fails", p, T, k)
    E = []
    Xprev = None
    for i in range(4):
        S = set(P)
        if i == 0: pass
        elif i < 3: S |= pick(rnd, Xprev, T - p)
        else:
            assert len(Xprev) <= T - p, ("X3 too big", len(Xprev), T - p)
            S |= Xprev
        assert len(S) <= T
        r = sm.reply(S)
        if r is None: info["outcome"] = "band"; return info
        e = sm.reps[r]; E.append(e)
        Xprev = (e - P) if i == 0 else (Xprev & e)
    seven = A + E
    ok = cover_ok(seven)
    info["outcome"] = "winD" if ok else "FAIL-COVER"
    info["maxreq"] = len(sm.reqs)
    return info


if __name__ == "__main__":
    params = [
        # (k, T, C, Lm)   Lm-1 = max lambda-overlap ; band [Lm, C]
        (40, 30, 24, 3),
        (60, 45, 36, 4),     # J3 tight in integers: (k-C) + 7(Lm-1) = T
        (50, 40, 31, 4),     # t=0.8
        (40, 36, 32, 5),     # t=0.9, J3 tight
        (60, 45, 40, 3),
    ]
    ngames = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    for (k, T, C, Lm) in params:
        assert k - C + 7 * (Lm - 1) <= T, "param violates integer J3"
        assert 2 * (Lm - 1) <= k - C and Lm <= 2 * C + 2 - k
        tally = {}; mm = [0, 0]
        for s in range(ngames):
            for pol in ("random", "new", "big", "small"):
                try:
                    info = play(k, T, C, Lm, s * 7 + hash(pol) % 1000, pol)
                except AssertionError as e:
                    info = {"outcome": "ASSERT:" + str(e)[:200], "maxreq": 0}
                key = info["outcome"]
                mm[0] = max(mm[0], info.get("m1", 0)); mm[1] = max(mm[1], info.get("m2", 0))
                tally[key] = tally.get(key, 0) + 1
                if key not in ("band", "win7", "winD"):
                    print("  !!", (k, T, C, Lm), s, pol, key, flush=True)
        print((k, T, C, Lm), tally, "max step1 req", mm[0], "max step2 req", mm[1], "T", T, flush=True)
