import json, collections, os
HERE = os.path.dirname(os.path.abspath(__file__))
rows = [json.loads(l) for l in open(os.path.join(HERE, 'out', 'results.jsonl'))]
def fm(r): return r['tau_b_frac'] if r['tau_b_frac'] != '-' else f"{r['tau_b']:.5f}"
def key(r): return (r['group'] if r['group'] != 'hash' else 'hash' + str(r['n']), r['n'], r['tau'], fm(r), r['atom_frac'], round(r['phi'], 4), r['symmetric'])
groups = collections.OrderedDict()
for r in rows:
    nm = r['name']
    if r['group'] == 'hash': nm = 'rule ' + nm.split(' (')[0].replace('rule ', '') ; 
    if r['group'] == 'task3' and 'U1' not in nm: nm = 'H1min/FKWmin/G\' ' + nm.replace('task3 ', '')
    groups.setdefault(key(r), []).append((nm, r))
out = ['| family | n | members | tau | tau*_b | margin 7/3 - tau*_b | max atom | Phi = min y(V)+7 max y | class |', '|---|---|---|---|---|---|---|---|---|']
for k, lst in groups.items():
    r = lst[0][1]; names = [a for a, _ in lst]
    nm = names[0] if len(names) == 1 else f'{names[0]} (+{len(names)-1} more with identical values, see appendix)'
    if r['group'] == 'hash': nm = f"hash/greedy rules at n={r['n']}: {len(names)} rule instances"
    if r['group'] == 'task3' and len(names) > 1 and 'U1' not in names[0]: nm = f'{len(names)} stored families (FKWmin, G\', 8 H1min orderings)'
    mem = f"{min(x['members'] for _, x in lst)}" + ('' if len(lst) == 1 or min(x['members'] for _, x in lst) == max(x['members'] for _, x in lst) else f"-{max(x['members'] for _, x in lst)}")
    sym = ' (orbit-avg)' if r['symmetric'] else ''
    out.append(f"| {nm}{sym} | {r['n']} | {mem} | {r['tau']} | {fm(r)} = {r['tau_b']:.4f} | {r['margin']:+.4f} | {r['max_atom']:.4f} ({r['atom_frac']}) | {r['phi']:.4f} | {'rich' if r['rich'] else 'thin'} |")
open(os.path.join(HERE, 'out', 'table_main.md'), 'w').write('\n'.join(out) + '\n')
app = ['| group | family | n | members | tau | tau*_b | margin | max atom | Phi | class |', '|---|---|---|---|---|---|---|---|---|---|']
for r in rows:
    app.append(f"| {r['group']} | {r['name']}{' (orbit-avg)' if r['symmetric'] else ''} | {r['n']} | {r['members']} | {r['tau']} | {fm(r)} | {r['margin']:+.4f} | {r['max_atom']:.4f} | {r['phi']:.4f} | {'rich' if r['rich'] else 'thin'} |")
open(os.path.join(HERE, 'out', 'table_full.md'), 'w').write('\n'.join(app) + '\n')
print(len(rows), len(groups))
