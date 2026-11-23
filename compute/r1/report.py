"""Markdown tables for notes/R1_RESULTS.md from out/grid_*.jsonl.   usage: py report.py"""
import json, glob, re, statistics

def fmt(p, den):
    return "(" + ",".join(("%.3f" % (v / den)).rstrip("0").rstrip(".") if v else "0" for v in p) + ")"

rows = []
for fn in sorted(glob.glob("out/grid_*.jsonl")):
    parts = re.split(r"[\/]", fn)[-1][:-6].split("_")
    variant, tstr, den, tail = parts[1], "_".join(parts[2:-2]), int(parts[-2]), parts[-1]
    R = [json.loads(l) for l in open(fn) if l.strip().endswith('}')]
    cnt = {"static": 0, "adaptive": 0, "None": 0, "other": 0}
    for r in R:
        k = str(r.get("win")) if "err" not in r else "other"
        cnt[k if k in cnt else "other"] += 1
    stuck = sorted(r["p"] for r in R if "err" not in r and r.get("win") is None)
    newp = [1 - sum(kv[:6]) for r in R if r.get("win") is None and "cuts" in r for kv, _ in r["cuts"]]
    big = 0; tot = 0
    for r in R:
        if r.get("win") is None and "cuts" in r:
            for kv, _ in r["cuts"]:
                tr = [kv[0] + kv[1] + kv[3], kv[0] + kv[2] + kv[4], kv[1] + kv[2] + kv[5]]
                tot += 1; big += max(tr) > 0.5 + 1e-9
    rows.append((variant, tstr.replace("_", "/"), den, tail, len(R), cnt, stuck, newp, big, tot, fn))

print("| variant | t | profile grid | profiles | static | adaptive | stuck | other | new points of recorded winning responses (min / median) | responses meeting an old edge in > 1/2 |")
print("|---|---|---|---|---|---|---|---|---|---|")
for variant, tstr, den, tail, n, cnt, stuck, newp, big, tot, fn in rows:
    np_ = f"{min(newp):.3f} / {statistics.median(newp):.3f}" if newp else "-"
    print(f"| {variant} | {tstr} | 1/{den}, {tail} | {n} | {cnt['static']} | {cnt['adaptive']} | {cnt['None']} | {cnt['other']} | {np_} | {big}/{tot} |")
print()
for variant, tstr, den, tail, n, cnt, stuck, newp, big, tot, fn in rows:
    print(f"**{variant}, t = {tstr}** ({fn.replace(chr(92), '/')}): stuck = " + (" ".join(fmt(p, den) for p in stuck) or "none"))
    print()
