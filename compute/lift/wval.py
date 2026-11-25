"""W(shape) = best first-order anchor-keeping certificate value among: static Theorem-B finish (MILP),
anchor-keeping Q' (LP, one adaptive request), Theorem D (p <= t - 1/3  <=>  value p + 1/3).
A shape is a proved anchored win at t if W <= t (static4 and Q are proved certificates; MILP/LP float)."""
import sys
from anchored_lp import static4
from qanchored import q_value

def W(shape, detail=False):
    p = sum(shape)
    vals = {'static': static4(shape), 'Q': q_value(*shape)[0], 'D': p + 1/3}
    best = min(vals.values())
    return (best, vals) if detail else best

if __name__ == '__main__':
    for sh in sys.argv[1:]:
        s = tuple(map(eval, sh.split(',')))
        b, v = W(s, True)
        print(tuple(round(x, 4) for x in s), 'p=%.3f N=%.3f' % (sum(s), 3 - sum(s)), 'W=%.4f' % b, {k: round(x, 4) for k, x in v.items()})
