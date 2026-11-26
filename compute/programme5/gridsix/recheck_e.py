"""Sound E-frame re-check (jm.stage2, SCIP) of stage1g INVULNERABLE answers when K meets E' (cell EpK):
jm gets Ep = |E' - K| only; EpK points are left out of the model entirely (his answers never use them, so every
jm trace is the true trace; her requests on them cannot matter in the E-frame, whose only EpK pairs are Z x EpK,
which jm ignores in his favour only... i.e. ignoring them can only help her, so an ADV stays sound).
usage: py recheck_e.py nproc  (all logs/ascan_*_e_*.json with result INVULNERABLE) -> logs/recheck_e.jsonl"""
import sys, os, json, glob
from multiprocessing import Pool
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'jointmilp'))
import jm
def work(fn):
    d = json.load(open(fn)); S0 = d['S']; m, o, bs = d['extra']
    SJ = {'X': S0['X'], 'Y': S0['Y'], 'A': S0['A'], 'B': S0['B'], 'Ep': S0['Ep'], 'Fd': S0['Fd'], 'Gd': S0['Gd']}
    m1 = {c: m.get(c, 0.0) for c in jm.C7}; o1 = o + m.get('OK', 0.0)
    v, info, it, _ = jm.stage2(SJ, m1, o1, d['t'], jm.SPEC, maxit=200, tl=120, wall=500)
    return {'file': os.path.basename(fn), 'EpK_in_M1': m.get('EpK', 0.0), 'stage2': v, 'it': it}
if __name__ == '__main__':
    pat = sys.argv[2] if len(sys.argv) > 2 else 'logs/ascan_*_e_*.json'
    fs = [f for f in glob.glob(pat) if json.load(open(f))['result'] == 'INVULNERABLE']
    with Pool(int(sys.argv[1])) as p, open('logs/recheck_e%s.jsonl' % (sys.argv[3] if len(sys.argv) > 3 else ''), 'w') as out:
        for r in p.imap_unordered(work, fs):
            out.write(json.dumps(r) + chr(10)); out.flush(); print(r, flush=True)
