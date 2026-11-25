r"""CORE 56.2: replay hash_check.py exactly (same RNG stream) and save every failing rule (orders + selector data) to a pickle,
so that the failures can be decided exactly (pencil_exact.py).  Usage: py hash_replay.py trials out.pkl"""
import sys, pickle, random
import hash_check as H
trials = int(sys.argv[1]); out = sys.argv[2]
rng = random.Random(644)
sizes = [(40, 31, 74), (40, 31, 76), (40, 31, 80), (40, 31, 88), (100, 76, 180), (100, 76, 190), (100, 76, 210)]
kinds = [("hash", 2), ("hash", 8), ("hash", 64), ("linear", 2), ("linear", 8), ("parity", 2), ("parity", 8), ("early", 2), ("early", 4),
         ("late", 2), ("late", 4), ("early^hash", 2), ("early^hash", 4), ("junta+", None), ("midhash", 2), ("midhash", 4)]
fails = []; tot = good = 0
for (k, T, n) in sizes:
    for kind, R in kinds:
        RR = R if R else T - k // 2 + 2
        for _ in range(trials):
            for mode in ("rand", "rev"):
                if mode == "rev" and RR != 2: continue
                orders = [rng.sample(range(n), n) for _ in range(RR)]
                if mode == "rev": orders[1] = orders[0][::-1]
                sel = H.make_selector(kind, n, k, T, RR, rng)
                rule = H.Rule(n, k, T, orders, sel)
                f, cover = H.solve(rule, rng, max_frames=(6000 if kind == "junta+" else 400), tries=(25 if kind == "junta+" else 60)); tot += 1
                good += cover
                if not cover:
                    cl = {nm: c.cell_contents for nm, c in zip(sel.__code__.co_freevars, sel.__closure__ or ())}
                    data = {k2: v for k2, v in cl.items() if isinstance(v, (list, int, bytes, set))}
                    fails.append(dict(k=k, T=T, n=n, kind=kind, R=RR, mode=mode, orders=orders, data=data))
                    print("FAIL", k, T, n, kind, RR, mode, sorted(data), flush=True)
print(f"TOTAL good sevens {good}/{tot}")
pickle.dump(fails, open(out, "wb"))
