r"""CORE 56.2: EXACT pencil decision for the junta+ greedy rules on which hash_check.py's random search failed.
Membership (parent criterion 55.1): K is a member iff for some class c there is an omega-set Z inside J_c(K) (the longest prefix of
order c contained in K) with sigma(K - Z) = c.  For the min-junta selector on W = (W_0..W_{w-1}) (class = first index i with W_i not in S,
class w if W is inside S) this is a disjunction of explicit options (see CORE 55.3); a pencil is a labelling of V by
{kernel, petal 1, 2, 3} with sizes n-3k/2, k/2, k/2, k/2 in which every line kernel+petal_i satisfies one option.  Encoded in SAT.
SAT -> a pencil exists (the search failure was a search failure); the labelling is then checked on the rule verbatim and
completed to a good seven by four transversal requests.  UNSAT -> no perfect pencil exists in the family [exact].
Usage: py pencil_exact.py fails.pkl
"""
import sys, pickle
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
import hash_check as H

def options(rule, W):
    n, om = rule.n, rule.om; w = len(W); opts = []
    for c in range(w + 1):
        o = rule.orders[c]; before = set(W[:c]) if c < w else set(W)
        cnt = 0; pref = []
        for x in o:
            pref.append(x)
            if x not in before:
                cnt += 1
                if cnt == om: break
        need_in = set(pref) | before
        if c < w:
            Wc = W[c]
            if Wc not in pref:                  # option A: W_c outside K
                opts.append((c, frozenset(need_in), Wc))
            pB = o[:max(o.index(Wc), len(pref) - 1) + 1]
            opts.append((c, frozenset(set(pB) | before), None))
        else:
            opts.append((c, frozenset(need_in), None))
    return opts

def decide(inst):
    k, T, n = inst["k"], inst["T"], inst["n"]; W = inst["data"]["W"]; R = inst["R"]
    rng = None
    sel = lambda rule, S: next((i % R for i, x in enumerate(W) if x not in S), len(W) % R)
    rule = H.Rule(n, k, T, inst["orders"], sel)
    opts = options(rule, W); ker = n - 3 * k // 2
    pool = IDPool(); lab = lambda x, j: pool.id(("l", x, j))      # j = 0 kernel, 1..3 petals
    cl = []
    for x in range(n):
        cl.append([lab(x, j) for j in range(4)])
        for a in range(4):
            for b in range(a + 1, 4): cl.append([-lab(x, a), -lab(x, b)])
    for j, size in enumerate([ker, k // 2, k // 2, k // 2]):
        e = CardEnc.equals(lits=[lab(x, j) for x in range(n)], bound=size, vpool=pool, encoding=EncType.seqcounter); cl += e.clauses
    for i in (1, 2, 3):
        ys = []
        for oi, (c, need, out) in enumerate(opts):
            y = pool.id(("o", i, oi)); ys.append(y)
            for x in need: cl.append([-y, lab(x, 0), lab(x, i)])
            if out is not None: cl.append([-y, -lab(out, 0)]); cl.append([-y, -lab(out, i)])
        cl.append(ys)
    s = Cadical153(bootstrap_with=cl)
    if not s.solve(): return False, None
    m = set(v for v in s.get_model() if v > 0)
    kap = set(x for x in range(n) if lab(x, 0) in m); P = [[x for x in range(n) if lab(x, j) in m] for j in (1, 2, 3)]
    # verify on the rule verbatim: each line is the reply to some request inside it, then complete to a good seven
    lines = [frozenset(kap | set(p)) for p in P]
    for K in lines:
        ok = False
        for c in range(len(rule.orders)):
            J = H.J(rule, c, K)
            for Z in [z for z in _cands(J, W, c, rule.om)]:
                if rule.reply(K - set(Z)) == K: ok = True; break
            if ok: break
        assert ok, "SAT labelling does not verify"
    seven = list(lines); halves = [(p[:k // 4], p[k // 4:]) for p in P]
    for tr in H.TRANS:
        S = set(x for i in range(3) for x in halves[i][tr[i]])
        for x in range(n):
            if len(S) >= T: break
            S.add(x)
        seven.append(rule.reply(S))
    cover = all(any(x in K and y in K for K in seven) for x in range(n) for y in range(x, n))
    return True, cover

def _cands(J, W, c, om):
    w = len(W); before = set(W[:c]) if c < w else set(W)
    free = [x for x in J if x not in before]
    if c < w and W[c] in J:
        rest = [x for x in free if x != W[c]][:om - 1]
        if len(rest) == om - 1: yield [W[c]] + rest
    elif len(free) >= om: yield free[:om]

if __name__ == "__main__":
    fails = pickle.load(open(sys.argv[1], "rb"))
    for inst in fails:
        ok, cover = decide(inst)
        print(f"k={inst['k']} T={inst['T']} n={inst['n']} {inst['kind']} R={inst['R']} |W|={len(inst['data']['W'])}: "
              f"perfect pencil {'EXISTS' if ok else 'DOES NOT EXIST [exact]'}" + (f"; verified on the rule, good seven: {cover}" if ok else ""), flush=True)
