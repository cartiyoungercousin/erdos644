"""Print out/eval.jsonl compactly."""
import json, os
for l in open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out', 'eval.jsonl')):
    d = json.loads(l)
    print(d['file'], 'N=%.3f' % (d['n'] / d['k']), 'g_start=%s g_fin=%.4f gA=%.4f gAlim=%.4f 4e=%.3f mincov=%d' % (('%.4f' % d['gamma_start']) if 'gamma_start' in d else '-', d['gamma_final'], d['gamma_a_finite'], d['gamma_a_limit'], d['four_eps'], d['min_cover_size_bound']))
    for key in ('start_seven', 'final_seven'):
        if key in d: s = d[key]; print('  ', key, 'cert %.5f±%.5f mp %.4g±%.2g' % (s['cert'], s['cert_se'], s['mean_prod'], s['mean_prod_se']))
    nr = d['noise_ref']; print('   noise', {a: round(b, 4) for a, b in nr.items() if a != 'seven'}, 'seven mp %.4g' % nr['seven']['mean_prod'])
    print('   complete mp %.4g depl start %s final %.3f noise %.3f' % (d['complete_mean_prod'], ('%.3f' % d['depletion_start']) if 'depletion_start' in d else '-', d['depletion_final'], d['depletion_noise_ref']))
