"""Print one line per snapshot of every SA log in out/."""
import json, glob, os
for f in sorted(glob.glob(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'log_*.txt'))):
    print('==', os.path.basename(f))
    for line in open(f):
        if line.startswith('{'):
            d = json.loads(line)
            print(d['it'], d['t'], d['size'], 'cert=%.5f mp=%.3f tr=%.3f' % (d['test_cert'], d['test_mean_prod'], d['train_cost']),
                  'codim', d['codimC'], 'rho', d['rho'], 'p1 %.3f p2 %.3f p3 %.3f' % (d['prop1'], d['prop2'], d['prop3']),
                  'dens1 %.3f' % d['dens1'], 'F %.3f %.3f %.3f %.3f' % (d['four_w1'], d['four_w2'], d['four_w3'], d['four_w4']), d.get('tau_b'))
        elif 'Error' in line: print(line.strip())
