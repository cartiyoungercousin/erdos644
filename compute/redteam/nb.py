"""Neighbourhood search around the proportional adversary at N ~ 2 (coordinator request).
For each adversary config (N, alphas, order) solve the requester's MILP at budget T' = T - 0.001 with her discard
fixed (drop 5 first, then others) until a line with z < 0 is found; each such line is then verified in exact
rational arithmetic at T (exact.py).  If every one of the 7 drops is solved to optimality with z > 0 the adversary
wins the modelled m = 8 game (float MILP; would then need exact confirmation and the unmodelled 7-reply test).
Usage: py nb.py worker_index   -> appends JSON lines to nb_<worker>.log"""
import sys, json, time, mix, exact
T = 0.76; TP = 0.759
C = [
 [(1.9, [1.0] * 6, "LOW"), (2.1, [1.0] * 6, "LOW"), (2.2, [1.0] * 6, "LOW"),
  (2.0, [1, 1, 0, 1, 1, 1], "LOW"), (2.0, [1, 1, 1, 1, 0, 1], "LOW"), (2.0, [1, 1, 1, 1, 1, 0], "LOW"), (2.0, [0, 1, 1, 1, 1, 1], "LOW")],
 [(2.0, [0.5] * 6, "LOW"), (2.0, [0.5] * 6, "HIGH"), (2.0, [0.8] * 6, "GIFT"), (2.0, [1, 0, 1, 0, 1, 0], "LOW"),
  (2.0, [0, 1, 0, 1, 0, 1], "LOW"), (2.0, [1, 1, 0, 1, 1, 1], "HIGH"), (2.0, [0.9] * 6, "LOW"), (2.0, [1, 1, 0.5, 1, 0.5, 1], "GIFT")],
]
if __name__ == "__main__":
    w = int(sys.argv[1]); out = open(f"nb_{w}.log", "a")
    for N, al, order in C[w]:
        al = [float(x) for x in al]; res = []; won = False; t0 = time.time()
        for drop, tl in ((5, 110), (1, 75), (2, 75), (7, 75), (3, 60), (4, 60), (6, 60)):
            if time.time() - t0 > 330: break
            st, zv, dr, bd, sol = mix.solve(TP, [N] * 7, al, order, tl, [drop])
            rec = dict(T=TP, Ns=[N] * 7, alphas=al, order=order, drops=[drop], status=st, z=zv, bound=bd, drop=dr, sol=sol)
            if zv is not None and zv < -0.0015:
                try:
                    ze, de, cov = exact.run(TP, [N] * 7, sol, al, order, 0.001)
                    rec["exact_z_at_T"] = str(ze); rec["exact_z_float"] = float(ze); rec["exact_drop"] = de
                    won = ze < 0
                except AssertionError as ex:
                    rec["exact_error"] = str(ex)
            out.write(json.dumps(rec) + "\n"); out.flush()
            res.append((drop, st, zv, bd))
            if won: break
        summ = dict(SUMMARY=True, N=N, alphas=al, order=order, verdict="REQUESTER wins (exact line)" if won else
                    ("ADVERSARY wins modelled game (all 7 drops optimal, z>0)" if len(res) == 7 and all(s == "Optimal" and z > 1e-6 for _, s, z, _ in res) else "UNDECIDED"),
                    runs=[(d, s, None if z is None else round(z, 4), round(b, 4)) for d, s, z, b in res], secs=round(time.time() - t0))
        out.write(json.dumps(summ) + "\n"); out.flush()
