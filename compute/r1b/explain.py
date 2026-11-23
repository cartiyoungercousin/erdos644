"""Show how the adversary holds a stuck anchor in the multi-round game.

usage: py explain.py T C DEPTH i,j,l [--pden 20] [--dden 40] [--cls all]
Re-solves the anchor at its own level with the top-level memo entry ignored (sub-positions come
from memo/), prints the recorded first responses K1 and, for each cell K1 avoids, the new good
triple q2 it would create and whether q2 is a won position at depth-1.
Writes out/explain_<...>.json (responses with their request-sealing patterns).
"""
import os, sys, json, argparse
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "r1"))
import multi

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("t"); ap.add_argument("c"); ap.add_argument("depth", type=int); ap.add_argument("q")
    ap.add_argument("--pden", type=int, default=20); ap.add_argument("--dden", type=int, default=40)
    ap.add_argument("--cls", default="half"); ap.add_argument("--extra", action="store_true")
    a = ap.parse_args()
    import game, game2
    ctx = multi.Ctx(a.t, a.c, a.pden, a.dden, cls=a.cls, extra=a.extra)
    q = tuple(int(v) for v in a.q.split(","))
    v = ctx.phi(q)
    key = f"{ctx.tag}_d{a.depth}_v{v:g}_{q[0]}_{q[1]}_{q[2]}"
    multi._mem.pop(key, None)
    fn = os.path.join(multi.MEMO, key)
    if os.path.exists(fn): os.remove(fn)
    ctx.record = {}
    res = ctx.wins(q, v, a.depth)
    print(f"anchor {q}/{a.pden}  t={a.t}  potential {ctx.pot} = {v / a.pden:g}  class={a.cls}  depth {a.depth}: {'WON' if res else 'STUCK'}")
    rr = ctx.record.get(key)
    if rr is None or "cuts" not in rr: sys.exit()
    mass = game.cell_mass(*(x / a.pden for x in q))
    print("cells X,Y,Z,PE,PF,PG =", [round(m, 3) for m in mass], f"; {len(rr['cuts'])} recorded responses answer all {rr.get('nreq')} grid requests")
    out = []
    for kv, losing in rr["cuts"]:
        kv = [float(x) for x in kv]
        tr = [kv[0] + kv[1] + kv[3], kv[0] + kv[2] + kv[4], kv[1] + kv[2] + kv[5]]
        info = []
        for c in range(3):
            if mass[c] > 1e-9 and kv[c] <= 1e-9:
                a_, b_ = game2.traces(mass, c, kv)
                q2 = tuple(sorted((round(mass[c] * a.pden, 3), round(a_ * a.pden, 3), round(b_ * a.pden, 3)), reverse=True))
                phi2 = ctx.phi(q2) / a.pden
                info.append(f"seal {'XYZ'[c]} -> triple {tuple(round(x / a.pden, 3) for x in q2)} Phi={phi2:.3f}")
        out.append(dict(K=[round(x, 4) for x in kv], traces=[round(x, 4) for x in tr], losing=[list(m) for m in losing], new=info))
    out.sort(key=lambda o: -o["K"][6])
    for o in out[:40]:
        print("  K1 =", o["K"], "|K&E|,|K&F|,|K&G| =", o["traces"], "; ".join(o["new"]))
    json.dump(dict(q=q, t=a.t, c=a.c, depth=a.depth, cls=a.cls, responses=out),
              open(os.path.join(HERE, "out", f"explain_{ctx.tag}_d{a.depth}_{q[0]}_{q[1]}_{q[2]}.json"), "w"))
