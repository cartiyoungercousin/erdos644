import sys, json; sys.path.insert(0, '../jointmilp'); import jm
d = json.load(open('logs/stage1g_YB_a6667o.json')); m, o, bs = d['extra']
S = {'X': 6.0, 'Y': 5.0, 'A': 6.667, 'B': 7.0, 'Ep': 3.0, 'Fd': 1.0, 'Gd': 2.333}
m1 = {c: m.get(c, 0.0) for c in jm.C7}; o1 = o + m.get('OK', 0.0)
print('M1', m1, 'o1', o1, flush=True)
res, info, it, _ = jm.stage2(S, m1, o1, 12 - 0.002, jm.SPEC, maxit=200, tl=120, wall=500)
print('stage2', res, it, info if res == 'REQ' else '')
