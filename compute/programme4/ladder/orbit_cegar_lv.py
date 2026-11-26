r"""Orbit CEGAR when the c-sets are too many to list (Rung 2, (k,n) = (16,32), PSL(2,31)).
Orbits and inclusion edges come from orbits_psl2.js (levels t = 3..c with canonical representatives, orbit sizes
checked against C(n,t)).  Covering clause for a T-orbit = the c-orbits reachable by c-T augmentation steps (any
c-superset of X is reached through a chain X < X+a < ... ; orbit level is enough since the family is invariant).
Outer SAT over c-orbits (Glucose 4, proof logging), minimal covering shrink, inner = randomised greedy over
sampled members (random chosen-orbit representative moved by a random group element); the orbit of every block is
known by construction, the seven is re-checked by plain code and cut.
Usage: py orbit_cegar_lv.py orbjson c T [maxiter] [seed] [tries] [sample]
"""
import sys, json, time, random, os
import numpy as np
from pysat.solvers import Solver
import groups as GR
from orbit_cegar import check_seven

HERE = os.path.dirname(os.path.abspath(__file__)); os.makedirs(os.path.join(HERE, "logs"), exist_ok=True)


def main():
    a = sys.argv[1:]
    D = json.load(open(a[0])); c, T = int(a[1]), int(a[2])
    maxiter = int(a[3]) if len(a) > 3 else 10 ** 7; seed = int(a[4]) if len(a) > 4 else 0
    tries = int(a[5]) if len(a) > 5 else 300; sample = int(a[6]) if len(a) > 6 else 4000
    q, n = D["q"], D["n"]; L = D["levels"]
    tag = f"oclv_psl2_{q}_{n}_{c}_{T}" + (f"_s{seed}" if seed else "")
    logf = open(os.path.join(HERE, "logs", tag + ".log"), "w")
    def log(*s):
        msg = " ".join(map(str, s)); print(msg, flush=True); logf.write(msg + "\n"); logf.flush()
    t0 = time.time(); rng = random.Random(seed); nr = np.random.default_rng(seed + 1)
    _, G = GR.psl2(q); G = np.array(G, dtype=np.int64); assert len(G) == D["order"]
    repC = np.array(L[c]["reps"], dtype=np.int64); sizes = np.array(L[c]["size"]); O = len(repC)
    log(f"PSL(2,{q}) order {len(G)}; c={c} (k={n-c}), T={T} (tau target {T+1}); c-orbits {O}; T-orbits {len(L[T]['reps'])}")
    # reachability T -> c
    reach = [{i} for i in range(len(L[T]["reps"]))]
    for t in range(T, c):
        E = L[t]["edges"]
        reach = [set(j for i in R for j in E[i]) for R in reach]
    clauses = [sorted(R) for R in reach]
    log(f"covering clauses {len(clauses)}, mean length {np.mean([len(x) for x in clauses]):.1f}, {time.time()-t0:.0f}s")
    cl_idx = np.concatenate([np.full(len(cl), i) for i, cl in enumerate(clauses)]); or_idx = np.concatenate([np.array(cl) for cl in clauses])
    srt = np.argsort(or_idx, kind="stable"); bounds = np.searchsorted(or_idx[srt], np.arange(O + 1))
    by_orb = [cl_idx[srt[bounds[o]:bounds[o + 1]]] for o in range(O)]
    bitsrep = np.array([[(int(r) >> x) & 1 for x in range(n)] for r in repC], dtype=np.int64)
    s = Solver(name="g4", with_proof=False)
    for cl in clauses: s.add_clause([o + 1 for o in cl])
    full = (1 << n) - 1; it = 0; cuts = []
    while it < maxiter:
        it += 1
        if not s.solve():
            log(f"UNSAT after {it-1} cuts: no PSL(2,{q})-invariant T-covering family without a good seven ({time.time()-t0:.0f}s)")
            json.dump({"clauses": clauses, "cuts": cuts}, open(os.path.join(HERE, "logs", tag + "_cert.json"), "w")); break
        model = s.get_model(); x = np.array([model[o] > 0 for o in range(O)], dtype=np.int64)
        cc = np.bincount(cl_idx, weights=x[or_idx], minlength=len(clauses)).astype(np.int64)
        order = [o for o in range(O) if x[o]]; rng.shuffle(order); order.sort(key=lambda o: -sizes[o])
        chs = set(order)
        for o in order:
            cls = by_orb[o]
            if np.all(cc[cls] > 1):
                chs.discard(o); cc[cls] -= 1
        chs = np.array(sorted(chs)); t1 = time.time(); sev = None
        for tr in range(tries):
            o0 = int(chs[tr % len(chs)]); blocks = [int(repC[o0])]; borb = [o0]
            U = [full & ~(1 << x) for x in range(n)]
            def cover(B):
                for x in range(n):
                    if B >> x & 1: U[x] &= ~B
            cover(blocks[0])
            while len(blocks) < 7 and any(U):
                ri = chs[nr.integers(0, len(chs), sample)]; g = G[nr.integers(0, len(G), sample)]
                bm = bitsrep[ri]; imgs = np.zeros(sample, dtype=np.int64)
                for x in range(n): imgs |= bm[:, x] << g[:, x]
                score = np.zeros(sample, dtype=np.int64)
                for x in range(n):
                    if U[x]: score += ((imgs >> x) & 1) * np.bitwise_count(imgs & U[x]).astype(np.int64)
                j = int(np.argmax(score))
                if score[j] == 0: break
                blocks.append(int(imgs[j])); borb.append(int(ri[j])); cover(int(imgs[j]))
            if not any(U): sev = (blocks, borb); break
        if sev is None:
            log(f"iter {it}: minimal covering family {len(chs)} orbits ({int(sizes[chs].sum())} co-edges): heuristic found no good seven in {tries} tries ({time.time()-t1:.0f}s) -> CANDIDATE, needs exact check")
            json.dump({"orbits": chs.tolist(), "reps": [int(repC[o]) for o in chs]}, open(os.path.join(HERE, "logs", tag + "_candidate.json"), "w"))
            break
        blocks, borb = sev
        assert check_seven(blocks, n) and all(bin(B).count("1") == c for B in blocks)
        os_ = sorted(set(borb)); cuts.append(os_); s.add_clause([-(o + 1) for o in os_])
        if it <= 5 or it % 50 == 0:
            log(f"iter {it}: family {len(chs)} orbits ({int(sizes[chs].sum())} co-edges), seven of {len(blocks)} blocks over {len(os_)} orbits, inner {time.time()-t1:.1f}s, total {time.time()-t0:.0f}s")
    logf.close()


if __name__ == "__main__":
    main()
