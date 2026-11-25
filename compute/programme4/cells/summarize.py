"""Tabulate certs/*.jsonl: per file, n range, #instances, statuses, cuts (total / max)."""
import glob, json, os
from collections import Counter
for fn in sorted(glob.glob('certs/*.jsonl')):
    rs = [json.loads(l) for l in open(fn)]
    if not rs: continue
    st = Counter(r['status'] for r in rs)
    ns = [r['n'] for r in rs]
    print(f"{os.path.basename(fn):28s} n {min(ns)}-{max(ns)}  inst {len(rs):4d}  {dict(st)}  cuts tot {sum(r.get('ncuts',0) for r in rs)} max {max(r.get('ncuts',0) for r in rs)}")
