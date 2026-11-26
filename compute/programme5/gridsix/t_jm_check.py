"""E-frame adaptive check (jm.stage2, SCIP) of a statically invulnerable M1 found by stage1g.  K's outside cell OK
and E'&K cell EpK are folded (OK -> outside, EpK -> Ep); both carry 0 or 0+ mass in the M1s checked here.
usage: py t_jm_check.py stage1g_json ka"""
import sys, json; sys.path.insert(0, '../jointmilp'); import jm
d = json.load(open(sys.argv[1])); m, o, bs = d['extra']; S0 = d['S']
S = {'X': S0['X'], 'Y': S0['Y'], 'A': S0['A'], 'B': S0['B'], 'Ep': S0['Ep'] + S0['EpK'], 'Fd': S0['Fd'], 'Gd': S0['Gd']}
m1 = {c: m.get(c, 0.0) for c in jm.C7}; m1['Ep'] += m.get('EpK', 0.0); o1 = o + m.get('OK', 0.0)
print('M1', {c: round(v, 4) for c, v in m1.items()}, 'o1', round(o1, 4), 'static', {k: round(v, 4) for k, v in bs.items()}, flush=True)
res, info, it, _ = jm.stage2(S, m1, o1, d['t'], jm.SPEC, maxit=200, tl=120, wall=500)
print('stage2', res, it, info if res == 'REQ' else '', flush=True)
