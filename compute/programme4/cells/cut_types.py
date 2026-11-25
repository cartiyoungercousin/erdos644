"""Classify the co-type supports used by the cuts: 'fano' if the support is 7 triples pairwise meeting in one
element (lines of a Fano plane), else by (support size, sorted type sizes). Also N = n/k vs 11/6."""
import glob, json, sys
from collections import Counter
def kind(sup):
    sup = sorted(set(sup))
    if len(sup) == 7 and all(bin(S).count('1') == 3 for S in sup) and all(bin(S & T).count('1') == 1 for S in sup for T in sup if S != T):
        return 'fano'
    return f"other{len(sup)}:" + ''.join(str(bin(S).count('1')) for S in sorted(sup, key=lambda S: bin(S).count('1')))
if __name__ == '__main__':
  for fn in sys.argv[1:]:
    c = Counter(); hi = Counter()
    for l in open(fn):
        r = json.loads(l)
        for cut in r['cuts']:
            sup = [int(S) for i in cut for S, v in cut[i].items() if v > 0]
            kd = kind(sup); c[kd] += 1
            if 6 * r['n'] >= 11 * r['k']: hi[kd] += 1
    print(fn, 'all:', c.most_common(5), '| n>=11k/6:', hi.most_common(5))
