"""status of kgen runs: last segment (after the last header line) of logs/kgen_<tag>.out"""
import sys
done = 0
for tag in sys.argv[1:]:
    L = open('logs/kgen_%s.out' % tag).read().splitlines()
    i = max(j for j, l in enumerate(L) if l.startswith('R0 '))
    seg = L[i + 1:]
    res = [l for l in seg if l.startswith('RESULT')]
    if res: done += 1
    print('%-4s %s | %s' % (tag, res[-1] if res else 'running', (seg[-1] if seg else '')[:110]))
print('finished', done, 'of', len(sys.argv) - 1)
