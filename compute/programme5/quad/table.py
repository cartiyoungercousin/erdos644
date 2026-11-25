"""Summarise logs/scan_k*.jsonl into the markdown table of PROGRAMME5_QUAD.md section 5."""
import json, glob, collections
rows = collections.defaultdict(list)
for f in sorted(glob.glob('logs/scan_k*.jsonl')):
    for line in open(f):
        if line.startswith('{'):
            r = json.loads(line); rows[(r['k'], r['n'])].append(r)
print('| k | n | c | level sets (q,a) | max τ | ⌊(3k+5)/4⌋ | #τ ≥ bound | Fano seven found / NONE / UNKNOWN (τ ≥ bound−1) | best τ with no Fano seven |')
print('|---|---|---|---|---|---|---|---|---|')
for (k, n), rs in sorted(rows.items()):
    b = (3 * k + 5) // 4
    tested = [r for r in rs if 'fano' in r]
    cnt = collections.Counter(r['fano'] for r in tested)
    nf = [r['tau'] for r in tested if r['fano'] == 'NONE']
    print(f"| {k} | {n} | {rs[0]['c']} | {len(rs)} | {max(r['tau'] for r in rs)} | {b} | {sum(r['tau'] >= b for r in rs)} | "
          f"{cnt['SEVEN']} / {cnt['NONE']} / {cnt['UNKNOWN']} | {max(nf) if nf else '–'} |")
