"""Read off the ending of the swap-adversary winning lines (same report as fano_read.py). Usage: py swap_read.py"""
import json, glob, swap, fano_read
for f in sorted(glob.glob("swap_[01].log")):
    for l in open(f):
        d = json.loads(l)
        if d.get("SUMMARY") or d.get("exact_z_float") is None or d["exact_z_float"] >= 0: continue
        d["Ns"] = [d["N"]] * 7; d["_sim"] = lambda dd: swap.simulate(dd)
        d["drop"] = [d.get("exact_drop", d["drop"][0])]
        print(f"##### swap at reply {d['w']}, q0={d['q0']}, exact mass(D)-T at T=0.76: {d['exact_z_float']:+.5f}")
        fano_read.report(d)
        m, real, hist = swap.simulate(d); nm = [str(i + 1) for i in range(7)]
        for e, (mm, ss) in enumerate(hist):
            print(f"   request {e+2}: " + " ".join(f"{fano_read.ts(J, nm)}:{ss[J]:.3f}/{mm[J]:.3f}" for J in sorted(mm, key=lambda J: -ss[J]) if ss[J] > 1e-6))
