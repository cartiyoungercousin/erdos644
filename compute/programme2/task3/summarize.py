import json, glob, collections, sys
rows = []
for f in sorted(glob.glob('logs/*.jsonl')):
    import os; suite = os.path.basename(f).split('_')[0]
    for l in open(f):
        r = json.loads(l); r['suite'] = suite; rows.append(r)
def short(x):
    if x is None: return None
    x = str(x); return x.split(':')[0] if not x.startswith('H2 fails at') else 'H2 fails (loads)'
for suite in sorted(set(r['suite'] for r in rows)) + ['ALL']:
    R = [r for r in rows if suite == 'ALL' or r['suite'] == suite]
    print(f'== {suite}: {len(R)} instances (H nonempty, V = union H)')
    L = [r for r in R if r['hyp_literal']]
    print('  literal hyp (any parity):', len(L), ' ground truth good:', sum(r['ilp'] == 'good' for r in L),
          ' none:', sum(r['ilp'] != 'good' for r in L), ' (of these with Wk>slack or None:', sum(r['ilp'] != 'good' and not r['hyp_k'] for r in L), ')')
    K = [r for r in R if r['hyp_k']]
    print('  parity-k hyp (H0+H1):', len(K), ' ground truth good:', sum(r['ilp'] == 'good' for r in K), ' none:', sum(r['ilp'] != 'good' for r in K))
    for key in ('cons', 'cons_brief', 'cons_ilp'):
        c = collections.Counter(short(r.get(key)) for r in K)
        print(f'    {key}:', dict(c))
    bad = [r for r in K if r['ilp'] != 'good']
    for r in bad[:8]:
        print('    NO-SEVEN under H0+H1:', r['name'], 'n', r['n'], 'k', r['k'], 'Wk', r['Wk'], 'slack', r['slack'], 'cells', r['cells'], r.get('cons'), r.get('sat_fano'), r.get('sat_any'))
    fails = [r for r in K if r['ilp'] == 'good' and r.get('cons_ilp') != 'ok']
    print('  good seven exists but structured construction (ILP Y-step) fails:', len(fails), collections.Counter(short(r.get('cons_ilp')) for r in fails))
    vf = [r for r in R if 'VERIFY' in str(r.get('cons')) + str(r.get('cons_brief')) + str(r.get('cons_ilp')) + r['ilp']]
    print('  verification failures:', len(vf))
