"""§15: exact verification of a strategy tree file + non-anticipativity self-check.
Checks: keys are exactly the 2^e bit prefixes of length e < R; every round's request is nonnegative and sums to <= T;
each leaf's request list is built ONLY from tree[prefix]; for every pair of leaves sharing a prefix of length e the
round-e requests are identical (recomputed from the per-leaf lists, not assumed).  Then exact replay of all 2^R leaves at
T (adaptive_m.replay: budget T, true tilt rule, best discard).
Usage: py adaptive_check.py T N R treefile outlog"""
import sys, json, itertools, adaptive_m as M


def check(T, N, R, tf, outlog):
    tree = {k: {int(J): v for J, v in r.items()} for k, r in json.load(open(tf)).items()}
    keys_ok = sorted(tree) == sorted("".join(p) for e in range(R) for p in itertools.product("UO", repeat=e))
    reqs_ok = all(min(r.values(), default=0) >= 0 and sum(r.values()) <= T for r in tree.values())
    leaves = ["".join(b) for b in itertools.product("UO", repeat=R)]
    per = {b: [dict(tree[b[:e]]) for e in range(R)] for b in leaves}
    na_viol = 0
    for e in range(R):
        grp = {}
        for b in leaves:
            g = grp.setdefault(b[:e], per[b][e])
            if g != per[b][e]:
                na_viol += 1
    rows = []
    for b in leaves:
        zq, d = M.replay(T, N, b, per[b], R)
        rows.append(dict(bits=b, margin_at_T=float(-zq), exact=str(-zq), drop=d))
    w = min(rows, key=lambda r: r["margin_at_T"])
    s = dict(keys_ok=keys_ok, requests_ok=reqs_ok, nonanticipativity_violations=na_viol, leaves=len(rows),
             won=sum(r["margin_at_T"] > 0 for r in rows), worst=[w["bits"], w["margin_at_T"], w["drop"]],
             worst_U=min(r["margin_at_T"] for r in rows if r["bits"][0] == "U"),
             worst_O=min(r["margin_at_T"] for r in rows if r["bits"][0] == "O"))
    with open(outlog, "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
        f.write(json.dumps(dict(SUMMARY=True, T=T, N=N, R=R, **s)) + "\n")
    return s


if __name__ == "__main__":
    print(json.dumps(check(float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5])))
