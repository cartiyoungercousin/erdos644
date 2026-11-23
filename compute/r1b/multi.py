"""R1b driver: multi-round re-anchoring game with a sparsest anchor (see game2.py).

usage: py multi.py T C DEPTH [--pden 20] [--dden 40] [--nproc 20] [--only i,j,l] [--xmax 0.5]
  T      budget (must satisfy T*dden integer), e.g. 0.8, 0.825, 0.775, 0.75
  C      the anchor minimizes C*s1 + s2 among good triples with all pair cells <= 1/2
  DEPTH  number of adaptive rounds allowed (1 = the one-round game of R1)
For every grid profile q (the possible anchors) decide whether q is in W(DEPTH, Phi(q)).
Results of sub-positions are memoized on disk (memo/), shared by all worker processes.
Output: out/multi_T_C_pden.jsonl  (one line per anchor: the smallest depth <= DEPTH that wins,
or null), summary on stdout.
"""
import os, sys, json, time, argparse
for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ.setdefault(_v, "1")
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "r1"))
from fractions import Fraction
from multiprocessing import Pool

MEMO = os.path.join(HERE, "memo")
_mem = {}


def memo_get(key):
    if key in _mem: return _mem[key]
    fn = os.path.join(MEMO, key)
    if os.path.exists(fn):
        try:
            v = open(fn).read().strip()
            if v in ("1", "0"):
                _mem[key] = v == "1"; return _mem[key]
        except OSError: pass
    return None


def memo_put(key, val):
    _mem[key] = val
    os.makedirs(MEMO, exist_ok=True)
    tmp = os.path.join(MEMO, key + f".{os.getpid()}.tmp")
    with open(tmp, "w") as f: f.write("1" if val else "0")
    try: os.replace(tmp, os.path.join(MEMO, key))
    except OSError: pass


class Ctx:
    def __init__(self, tstr, c, pden, dden, max_outer=1500, cls="half", extra=False):
        self.tstr, self.t, self.pden, self.dden, self.max_outer = tstr, float(Fraction(tstr)), pden, dden, max_outer
        # c: a number (potential c*s1 + s2) or a string "c1,c2,c3" (potential c1*s1 + c2*s2 + c3*s3)
        cs = str(c)
        self.pot = tuple(float(v) for v in cs.split(",")) if "," in cs else (float(c), 1.0, 0.0)
        self.c = self.pot[0] if self.pot[1:] == (1.0, 0.0) else None
        self.cname = ("%g" % self.pot[0]) if self.c is not None else "p" + "_".join("%g" % v for v in self.pot)
        self.cls = cls
        self.tag = f"{tstr.replace('/', '_')}_{self.cname}_{pden}_{dden}" + ("" if cls == "half" else "_" + cls) + ("_gapB" if extra else "")
        self.extra = extra

    def valid(self, q):
        i, j, l = q
        return (i >= j >= l >= 0 and i >= 1 and (2 * i <= self.pden or self.cls == "all") and i + j <= self.pden
                and (i + j + l) / self.pden <= 3 - 2 * self.t + 1e-9)

    def phi(self, q):                      # Phi * pden
        return self.pot[0] * q[0] + self.pot[1] * q[1] + self.pot[2] * q[2]

    def wins(self, q, vnum, depth):
        """is position q in W(depth, v)?  v = vnum / pden."""
        import game, outer, game2
        if not self.valid(q): return False
        if self.phi(q) < vnum - 1e-9: return True                  # q itself contradicts minimality
        # Lemma A (Lean644/SparserTriple.lean): an anchor with x + 2y > 2 - t has a sparser class
        # triple (largest cell <= x, two largest cells sum < x + y), a contradiction for every
        # potential c*s1 + s2 with c >= 1.  Only valid at the anchor's own level.  (The request
        # grid can miss it: the lemma needs D_E = D_G = (t - y)/2, a half grid step.)
        if abs(self.phi(q) - vnum) < 1e-9 and self.pot[2] == 0 and self.pot[0] >= self.pot[1] > 0 and (q[0] + 2 * q[1]) / self.pden > 2 - self.t + 1e-9 \
                and 2 * q[0] <= self.pden:
            return True
        key =f"{self.tag}_d{depth}_v{vnum:g}_{q[0]}_{q[1]}_{q[2]}"
        r = memo_get(key)
        if r is not None: return r
        if depth > 1 and self.wins(q, vnum, depth - 1):
            memo_put(key, True); return True
        x, y, z = (a / self.pden for a in q)
        rules = game.Rules(3 - 2 * self.t, pot=tuple(-v for v in self.pot), pot0=-vnum / self.pden, half=(self.cls == "half"))
        if self.extra:
            # (i) Lemma B w.r.t. the current good triple (valid for every edge of the family).
            U = 3 - (x + y + z)
            if 3 * self.t - U > 0: rules.lemB = (3 * self.t - U) / 2
            # (ii) pair gap for the potential c*s1 + s2, class = all: if two edges A, B meet in m points,
            # the request (A & B) + (t-m)/2 points of each of A-B, B-A gives a good triple with cells
            # m, <= w, <= w, w = (2-t-m)/2, whose potential is at most g(m) = c*m + w (m >= w) or
            # (c+1)*w (m < w); g(m) < v contradicts the minimality of the anchor.  So no pair
            # intersection lies strictly between m_lo and m_hi.
            if self.c is not None and self.cls == "all":
                c_ = self.c; v = vnum / self.pden; T2 = 2 - self.t
                if (c_ + 1) * T2 / 3 < v - 1e-9:
                    rules.gap = (T2 - 2 * v / (c_ + 1), min((v - T2 / 2) / (c_ - 0.5), self.t))
        kden = None
        if depth > 1:
            kd = self.dden; step = kd // self.pden
            cache = {}
            def lookup(mc, i, j, self=self, vnum=vnum, depth=depth, cache=cache, kd=kd, step=step):
                m = round(mc * self.pden)
                k3 = (m, i, j)
                if k3 in cache: return cache[k3]
                ai = [i // step] if i % step == 0 else [i // step, i // step + 1]
                bj = [j // step] if j % step == 0 else [j // step, j // step + 1]
                res = True
                for a in ai:
                    for b in bj:
                        q2 = tuple(sorted((m, a, b), reverse=True))
                        if not self.wins(q2, vnum, depth - 1): res = False; break
                    if not res: break
                cache[k3] = res
                return res
            rules.lookup = lookup; rules.kden = kd; kden = kd
        try:
            rr = outer.solve_profile(x, y, z, self.t, rules, den=self.dden, max_outer=self.max_outer, kden=kden)
            res = rr["win"] in ("static", "adaptive")
            if getattr(self, "record", None) is not None: self.record[key] = rr
        except Exception as e:
            sys.stderr.write(f"ERR {key}: {e!r}\n"); res = False
        memo_put(key, res)
        return res


def work(job):
    tstr, c, pden, dden, q, depth, cls, extra = job
    ctx = Ctx(tstr, c, pden, dden, cls=cls, extra=extra)
    t0 = time.time()
    v = ctx.phi(q)
    for d in range(1, depth + 1):
        if ctx.wins(q, v, d): return dict(p=list(q), win=d, sec=round(time.time() - t0, 1))
    return dict(p=list(q), win=None, sec=round(time.time() - t0, 1))


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("t"); ap.add_argument("c"); ap.add_argument("depth", type=int)
    ap.add_argument("--pden", type=int, default=20); ap.add_argument("--dden", type=int, default=40)
    ap.add_argument("--nproc", type=int, default=20); ap.add_argument("--only", default=None)
    ap.add_argument("--extra", action="store_true", help="add Lemma B and the pair gap as constraints on every response")
    ap.add_argument("--list", default=None, help="semicolon separated anchors i,j,l;i,j,l;...")
    ap.add_argument("--cls", default="half", help="half: anchors/class = good triples with all pair cells <= 1/2; all: no restriction")
    a = ap.parse_args()
    ctx = Ctx(a.t, a.c, a.pden, a.dden, cls=a.cls, extra=a.extra)
    assert abs(ctx.t * a.dden - round(ctx.t * a.dden)) < 1e-9, "T*dden must be an integer"
    import tables
    for q in range(27): tables.fast_index("quad", (q // 9, q // 3 % 3, q % 3))
    for ab in [(), (0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]: tables.fast_index("triple", ab)
    if a.list:
        qs = [tuple(int(v) for v in q.split(",")) for q in a.list.split(";")]
    elif a.only:
        qs = [tuple(int(v) for v in a.only.split(","))]
    else:
        qs = [(i, j, l) for i in range(1, a.pden + 1) for j in range(0, i + 1) for l in range(0, j + 1) if ctx.valid((i, j, l))]
    jobs = [(a.t, a.c, a.pden, a.dden, q, a.depth, a.cls, a.extra) for q in sorted(qs, key=lambda q: -sum(q))]
    fn = os.path.join(HERE, "out", f"multi_{ctx.tag}_depth{a.depth}" + ("_list" if a.list else "") + ".jsonl")
    cnt = {}; stuck = []; t0 = time.time()
    with Pool(a.nproc) as pool, open(fn, "w") as f:
        for r in pool.imap_unordered(work, jobs, chunksize=1):
            f.write(json.dumps(r) + "\n"); f.flush()
            k = str(r["win"]); cnt[k] = cnt.get(k, 0) + 1
            if r["win"] is None: stuck.append(tuple(v / a.pden for v in r["p"]))
    print(f"t={a.t} potential={ctx.pot} class={a.cls} depth<={a.depth} grid 1/{a.pden} (requests 1/{a.dden}): {len(jobs)} anchors; "
          f"won at depth: {dict(sorted((k, v) for k, v in cnt.items() if k != 'None'))}; stuck {cnt.get('None', 0)}: {sorted(stuck)}; "
          f"time {round(time.time() - t0)}s", flush=True)
