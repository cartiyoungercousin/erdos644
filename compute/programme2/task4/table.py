r"""Print the Task 4 tables (markdown) from out/measure.jsonl, out/struct.jsonl, out/selectors.jsonl."""
import json, os
HERE = os.path.dirname(os.path.abspath(__file__))
def load(f):
    p = os.path.join(HERE, 'out', f); return [json.loads(l) for l in open(p)] if os.path.exists(p) else []
seen = {}
for r in load('measure.jsonl'): seen[r['name']] = r
struct = {r['name']: r for r in load('struct.jsonl')}
def ann(nm, r):
    s = struct.get(nm)
    if not s: return ''
    out = []
    for a in s['ann_supports']:
        out.append('all' if a and a[0] == 'complement of' and a[1] == [] else ('compl(%s)' % ','.join(map(str, a[1])) if a and a[0] == 'complement of' else '{%s}' % ','.join(map(str, a))))
    return ' '.join(out)
def trip(r, nm):
    z = r.get('zero_triples', struct.get(nm, {}).get('triples_x1+x2=x3'))
    t = r['triple_min']
    ex = r['triple_exact'] or t == r['rho'] or (r['k_sizes'].keys() == {str(r['k'])} and r['k'] % 2 == 0 and t == 2 and z == 0)
    return f"{t}{'' if ex else '*'}"
def row(r):
    nm = r['name']; ch = r.get('chain'); chs = '; '.join(f"{c['kept']:.3f}/{c['rho']}" for c in ch[:2]) if ch else 'n/a'
    f = r.get('fano', {})
    fs = f"{f['min_sum_wt']} / {f['lemma5_budget']} [{f['colourings_ok']}/{f['colourings_tried']}]" if f.get('colourings_ok') else f"none [0/{f.get('colourings_tried')}]"
    z = r.get('zero_triples', struct.get(nm, {}).get('triples_x1+x2=x3'))
    return f"| {nm} | {r['n']} | {r['members']} | {r['k']} | {r['tau']} | {r['dim_C']} | {r['rho']} | {ann(nm, r)} | {r['four_T_minus_3k']} | {trip(r, nm)} | {'' if z is None else z} | {r['budget_3_4n_7k']} | {'yes' if r['cor7'] else 'no'} | {chs} | {fs} |"
hdr = ('| family | n | #H | k | tau | dim C | rho | checks of C^perp | 4T-3k | min triple | #(x1+x2=x3) | 3(4n-7k) | 7rho>bud | coset frac / rho (2 steps) | Fano: min sum wt / Lemma-5 bud [ok/tried] |\n' + '|' + '---|' * 15)
groups = {}
for nm, r in seen.items(): groups.setdefault(r['group'], []).append(r)
for g in ('fkw', 'ctrl', 'h1', 'task3', 'k8', 'sel', 'k10', 'k13', 'nearpool', 'complete'):
    if g in groups:
        print(f'\n**{g}**\n\n' + hdr)
        for r in groups[g]: print(row(r))
H = groups.get('hash', [])
if H:
    import collections
    print(f'\n**hash/greedy rules (CORE 56): {len(H)} families**, n in {{15,16}}, k = 8, T = 6')
    print('rho values:', dict(collections.Counter(r['rho'] for r in H)), '; codim:', dict(collections.Counter(r['codim'] for r in H)))
    print('dim C:', dict(collections.Counter(r['dim_C'] for r in H)))
    ok = [r for r in H if r['fano'].get('colourings_ok')]
    print('families with a Fano-type seven found:', len(ok), '; min Fano sum wt / budget:', collections.Counter((r['fano']['min_sum_wt'], r['fano']['lemma5_budget']) for r in ok).most_common(8))
    print('coset frac after step 1 (min, median, max):', min(r['chain'][0]['kept'] for r in H), sorted(r['chain'][0]['kept'] for r in H)[len(H)//2], max(r['chain'][0]['kept'] for r in H))
    print('families whose step-1 coset has rho>0 and kept>=0.8:', [(r['name'], r['chain'][0]['kept'], r['chain'][0]['rho']) for r in H if r['chain'][0]['kept'] >= 0.8 and r['chain'][0]['rho'] > 0])
    print('families with no Fano seven found:', [r['name'] for r in H if not r['fano'].get('colourings_ok')])
