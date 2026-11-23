"""Summaries of out/grid_*.jsonl.   usage: py summarize.py [file ...]"""
import sys, json, glob

def load(fn):
    return [json.loads(l) for l in open(fn)]

def summary(fn):
    R = load(fn); den = int(fn.replace("\\", "/").split("_")[-2])
    cnt = {}
    for r in R:
        k = "ERR" if "err" in r else str(r["win"]); cnt[k] = cnt.get(k, 0) + 1
    print(f"== {fn}: {len(R)} profiles {cnt}")
    stuck = sorted(r["p"] for r in R if "err" not in r and r["win"] is None)
    und = sorted(r["p"] for r in R if "err" in r or r["win"] == "undecided")
    fmt = lambda p: "(" + ",".join(f"{v / den:.2f}".rstrip("0").rstrip(".") if v else "0" for v in p) + ")"
    print("   stuck:", " ".join(fmt(p) for p in stuck))
    if und: print("   undecided/error:", " ".join(fmt(p) for p in und))
    return R

if __name__ == "__main__":
    for fn in (sys.argv[1:] or sorted(glob.glob("out/grid_*.jsonl"))): summary(fn)
