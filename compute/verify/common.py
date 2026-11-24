"""Independent verifier harness for PETAL 20.2 (DS), 21.1 (DS-b), 23.2 (AP).  Written from the statements only.

Ground set = region 0 (R_X, nx points) + region 1 (R_Y, ny points) + optional pool region 2 (m points).
A reply = k points disjoint from the request S, with >= k - rho_c points in region c for some class c
(the rest anywhere outside S, including in either region or the pool).
Adversary = family of replies chosen by a priority vector w (parametrised genome); hill-climbed to maximise
max pair coverage (7 = a 2-cover of the seven replies exists = requester loses).
"""
import random, itertools


def cover_stats(sets, N):
    """max number of sets covered by two points; returns (maxcov, n_sets)."""
    m = len(sets)
    mask = [0] * N
    for j, s in enumerate(sets):
        for x in s:
            mask[x] |= 1 << j
    ms = sorted(set(mask))
    best = 0
    for a in range(len(ms)):
        for b in range(a, len(ms)):
            c = bin(ms[a] | ms[b]).count("1")
            if c > best:
                best = c
    return best


def has_2cover(sets, N):
    return cover_stats(sets, N) == len(sets)


class Family:
    def __init__(self, k, nx, ny, rho, pool=0):
        self.k = k
        self.n = [nx, ny]
        self.rho = list(rho)
        self.pool = pool
        self.N = nx + ny + pool
        self.reg = [0] * nx + [1] * ny + [2] * pool
        self.R = [set(range(nx)), set(range(nx, nx + ny)), set(range(nx + ny, self.N))]
        self.allpts = set(range(self.N))

    def cls_of(self, E):
        """classes (0,1) the set E belongs to."""
        return [c for c in (0, 1) if len(E & self.R[c]) >= self.k - self.rho[c]]

    def feasible_classes(self, S):
        out = []
        for c in (0, 1):
            if len(self.R[c] - S) >= self.k - self.rho[c] and len(self.allpts - S) >= self.k:
                out.append(c)
        return out

    def tau(self, c):
        return self.n[c] - self.k + self.rho[c]

    def cmin(self, c):
        return 2 * (self.k - self.rho[c]) - self.n[c]


class Adv:
    """Adversary with genome = list of per-step dicts; deterministic given genome."""

    def __init__(self, fam, genome):
        self.fam = fam
        self.g = genome
        self.step = 0
        self.reps = []
        self.reqs = []
        self.cls = []

    def reply(self, S):
        fam = self.fam
        k = fam.k
        g = self.g[min(self.step, len(self.g) - 1)]
        self.step += 1
        self.reqs.append(set(S))
        fc = fam.feasible_classes(S)
        if not fc:
            return None
        if len(fc) == 1:
            c = fc[0]
        else:
            mode = g["cmode"]
            if mode in (0, 1):
                c = mode
            else:  # balance: pick class with fewer replies so far (mode 2) / more (mode 3)
                cnt = [self.cls.count(0), self.cls.count(1)]
                c = 0 if (cnt[0] <= cnt[1]) == (mode == 2) else 1
        rnd = random.Random(g["seed"] + 1000 * self.step)
        N = fam.N
        f1 = [0] * N
        f2 = [0] * N
        f3 = [0] * N
        f4 = [0] * N
        for E, cc in zip(self.reps, self.cls):
            for x in E:
                f1[x] += 1
                if cc == c:
                    f2[x] += 1
        if self.reps:
            for x in self.reps[-1]:
                f3[x] = 1
        for R in self.reqs[:-1]:
            for x in R:
                f4[x] += 1
        w = [g["a"][0] * f1[i] + g["a"][1] * f2[i] + g["a"][2] * f3[i] + g["a"][3] * f4[i] + g["noise"] * rnd.random()
             for i in range(N)]
        # own part: k - rho_c points of region c outside S with highest w
        own_c = sorted(fam.R[c] - S, key=lambda i: -w[i])[:k - fam.rho[c]]
        E = set(own_c)
        # leak part: the rest, highest w anywhere outside S (leak-sign flips w for leak via g['lsign'])
        rest = sorted(fam.allpts - S - E, key=lambda i: -g["lsign"] * w[i])
        # optionally prefer other region
        if g["leakreg"] is not None:
            rest.sort(key=lambda i: (fam.reg[i] != g["leakreg"],))  # stable: region preferred first
        E |= set(rest[:k - len(E)])
        assert len(E) == k and not (E & S)
        self.reps.append(E)
        self.cls.append(c)
        return E


def rand_genome(rnd, steps=10):
    g = []
    for _ in range(steps):
        g.append(dict(cmode=rnd.choice([0, 1, 2, 3]), seed=rnd.randrange(10 ** 6),
                      a=[rnd.choice([-3, -1, 0, 1, 3]) * rnd.random() for _ in range(4)],
                      noise=rnd.choice([0.1, 1, 5]), lsign=rnd.choice([1, -1]),
                      leakreg=rnd.choice([None, 0, 1, 2])))
    return g


def mutate(g, rnd):
    g2 = [dict(x, a=list(x["a"])) for x in g]
    for _ in range(rnd.choice([1, 1, 2, 3])):
        s = rnd.randrange(len(g2))
        r = rnd.random()
        if r < 0.2:
            g2[s]["cmode"] = rnd.choice([0, 1, 2, 3])
        elif r < 0.4:
            g2[s]["seed"] = rnd.randrange(10 ** 6)
        elif r < 0.7:
            g2[s]["a"][rnd.randrange(4)] = rnd.choice([-3, -1, 0, 1, 3]) * rnd.random()
        elif r < 0.8:
            g2[s]["lsign"] *= -1
        elif r < 0.9:
            g2[s]["leakreg"] = rnd.choice([None, 0, 1, 2])
        else:
            g2[s]["noise"] = rnd.choice([0.1, 1, 5])
    return g2


def run_search(fam, strategy, T, games, seed, steps=10, verbose=False):
    """strategy(fam, T, ask) -> dict(replies, requests, ...) ; returns summary over adversary search."""
    rnd = random.Random(seed)
    best = None
    stats = dict(games=0, wins=0, loses=0, budget_viol=0, flags=[], maxreq=0, maxcov=0)

    def play(g):
        adv = Adv(fam, g)
        out = strategy(fam, T, adv.reply)
        stats["games"] += 1
        reps = out["replies"]
        mc = cover_stats(reps, fam.N) if len(reps) == 7 else -1
        mr = max((len(r) for r in out["requests"]), default=0)
        stats["maxreq"] = max(stats["maxreq"], mr)
        if out.get("flags"):
            stats["flags"].extend(out["flags"])
        if mr > T:
            stats["budget_viol"] += 1
        if len(reps) == 7 and mc == 7:
            stats["loses"] += 1
        elif len(reps) == 7:
            stats["wins"] += 1
        stats["maxcov"] = max(stats["maxcov"], mc)
        return (mc if not out.get("flags") else 8, mr), out

    pop = []
    for _ in range(games // 2):
        g = rand_genome(rnd, steps)
        sc, out = play(g)
        pop.append((sc, g))
    pop.sort(key=lambda x: -(x[0][0] * 10000 + x[0][1]))
    cur = pop[:5]
    for it in range(games - games // 2):
        sc, g = rnd.choice(cur)
        g2 = mutate(g, rnd)
        sc2, out = play(g2)
        cur.append((sc2, g2))
        cur.sort(key=lambda x: -(x[0][0] * 10000 + x[0][1]))
        cur = cur[:5]
    stats["best"] = cur[0][0]
    return stats
