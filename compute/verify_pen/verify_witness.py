"""Plain re-check of a SAT witness (no numpy/pysat): covering and min pencil weight.
usage: verify_witness.py logfile n k r"""
import sys, itertools, ast
f, n, k, r = sys.argv[1], *map(int, sys.argv[2:5])
W = ast.literal_eval(open(f).read().split('witness:')[1].strip())
H = [frozenset(x) for x in W]; assert all(len(x) == k for x in H) and len(set(H)) == len(H)
cov = all(any(x <= set(c) for x in H) for c in itertools.combinations(range(n), k + r))
ws = sorted({len(a ^ b ^ c) for a, b, c in itertools.combinations(H, 3) if not (a & b & c)})
print(f"|H|={len(H)} (k+r)-covering={cov} pencil weights present={ws}")
