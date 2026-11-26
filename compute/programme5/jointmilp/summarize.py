r"""Summarise a certificate file logs/cover_<tag>.jsonl.  usage: py -3.14 summarize.py alpha delta"""
import sys, os, json
import numpy as np
import jm
AL, DE = float(sys.argv[1]), float(sys.argv[2])
S = jm.sizes(AL)
HERE = os.path.dirname(os.path.abspath(__file__))
rows = [json.loads(l) for l in open(os.path.join(HERE, 'logs', 'cover_a%g_d%g.jsonl' % (AL, DE)))]
res = {}
for d in rows: res[d['res']] = res.get(d['res'], 0) + 1
adv = [d for d in rows if d['res'] == 'ADV']
print('states decided:', res)
its = [d['it'] for d in adv]; secs = [d['sec'] for d in adv]; np_ = [len(d['cert']) for d in adv]
print('ADV states: CEGAR iterations median %d max %d; patterns median %d max %d; solver time total %.0fs max %.0fs'
      % (np.median(its), max(its), np.median(np_), max(np_), sum(secs), max(secs)))
live = lambda d: sum(d['M1'][:4])
print('live mass kept by M1 over ADV states: min %.3f max %.3f' % (min(map(live, adv)), max(map(live, adv))))
rq = [d for d in rows if d['res'] == 'REQ']
for d in rq[:10]: print('REQ state', [round(x, 3) for x in d['M1']], 'R2', {k: round(v, 3) for k, v in d['R2'][0].items()}, round(d['R2'][2], 3))
