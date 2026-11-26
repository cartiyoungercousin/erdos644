import sys, json, time, multiprocessing as mp
sys.argv = ['run_stage.py', sys.argv[1], sys.argv[2], '0.002', '1']
import run_stage as R, jm
def f(r):
    o = jm.oracle1(R.S, dict(zip(jm.C7, r)), jm.SPEC, wpad={'Ep': 1e-3, 'Fd': 1e-3, 'Gd': 1e-3})
    m1, o1 = o
    return r, tuple(round(m1[c], 4) for c in jm.C7) + (round(o1, 4),), sum(R.S[c] - r[i] - m1[c] for i, c in enumerate(jm.C7[:4]))
if __name__ == '__main__':
    reqs = R.requests(); t0 = time.time()
    with mp.Pool(12) as p: out = p.map(f, reqs, chunksize=50)
    st = {}
    for r, k, d in out: st.setdefault(k, []).append(r)
    nd = sum(1 for r, k, d in out if d > 1e-6)
    print(len(reqs), 'requests', len(st), 'distinct M1 states', nd, 'with forced drops', '%.0fs' % (time.time() - t0))
    json.dump([[list(k), v] for k, v in st.items()], open('logs/states_a%s_h%s.json' % (sys.argv[1], sys.argv[2]), 'w'))
