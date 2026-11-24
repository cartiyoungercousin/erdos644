import sys, os, json
here = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(here, "..", "r1b")); sys.path.insert(0, os.path.join(here, "..", "r1"))
import multi
multi.memo_get = lambda k: None; multi.memo_put = lambda k, v: None
q = tuple(int(v) for v in sys.argv[2].split(","))
ctx = multi.Ctx(sys.argv[1], "1,1,1", 25, 50, cls="all"); ctx.record = {}
print(ctx.wins(q, ctx.phi(q), 1))
for k, rr in ctx.record.items(): print(k, json.dumps(rr, default=str)[-1200:])
