import sys, time
from endgame import solve, popc
asc = lambda i, types: sorted(types, key=lambda J: (popc(J), J))
T = float(sys.argv[1])
for N in [float(x) for x in sys.argv[2:]]:
    t0 = time.time()
    st, val, info = solve(T, "req_free", adv_order=asc, N=N, pool_first=True, tl=240)
    print(f"T={T} LOW-degree-first adversary on ground set N={N}: status={st} min mass(D)={val} bound={info and info['bound']} -> {'REQUESTER wins' if val is not None and val <= T + 1e-6 else 'adversary wins'} [{time.time()-t0:.0f}s]", flush=True)
    if info:
        print("   final:", info["final"])
        for i, h in enumerate(info["hist"], start=2):
            print(f"   edge {i}: request {h['req']}  take {h['take']} fresh {h['fresh']}")
