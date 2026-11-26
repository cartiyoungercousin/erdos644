r"""Decide one M1 state exactly and append its certificate line to logs/cover_<tag>.jsonl.
usage: py -3.14 save_cert.py alpha delta m1(8 comma values: X,Y,A,B,Ep,Fd,Gd,o1) [maxit]"""
import sys, os, json, time
import jm
AL, DE = float(sys.argv[1]), float(sys.argv[2]); st = [float(x) for x in sys.argv[3].split(',')]
MAXIT = int(sys.argv[4]) if len(sys.argv) > 4 else 300
S = jm.sizes(AL); T = 12 - DE; HERE = os.path.dirname(os.path.abspath(__file__))
t0 = time.time()
res, info, it, _ = jm.stage2(S, dict(zip(jm.C7, st[:7])), st[7], T, jm.SPEC, maxit=MAXIT, tl=170, log=(lambda s: print(s, flush=True)))
out = {'M1': st, 'res': res, 'it': it, 'sec': round(time.time() - t0, 1), 'src': 'save_cert'}
if res == 'ADV': out['cert'] = [[{'%s%d' % k: v for k, v in P.items() if v > 0}, PO] for P, PO in info]
if res == 'REQ': out['R2'] = [{'%s%d' % k: v for k, v in info[0].items() if v > 1e-7}, info[1], info[2][0]]
with open(os.path.join(HERE, 'logs', 'cover_v3_a%g_d%g.jsonl' % (AL, DE)), 'a') as f: f.write(json.dumps(out) + '\n')
print(st, res, 'it', it, '%.0fs' % (time.time() - t0), 'patterns', len(info) if res == 'ADV' else out.get('R2'))
