"""Adversary best response (exact MILP) against several fixed-priority requester policies."""
import sys, time
from endgame import solve, popc
orders = {
 "deg desc, lex asc":  lambda i, t: sorted(t, key=lambda J: (-popc(J), J)),
 "deg desc, newest first": lambda i, t: sorted(t, key=lambda J: (-popc(J), -J)),
 "deg desc, oldest-edge types last": lambda i, t: sorted(t, key=lambda J: (-popc(J), J & 1, J)),
 "deg>=2 newest first, then deg1 newest": lambda i, t: sorted(t, key=lambda J: (popc(J) < 2, -J)),
 "deg desc, ties left to adversary": None,
}
for T in [float(x) for x in sys.argv[1:]]:
    for name, o in orders.items():
        t0 = time.time()
        if o is None:
            st, val, info = solve(T, "adv_free", req_order=orders["deg desc, lex asc"], req_ties="degree", tl=120)
        else:
            st, val, info = solve(T, "adv_free", req_order=o, tl=120)
        print(f"T={T} requester policy [{name}]: {st} max mass(D)={val:.4f} (bound {info['bound']:.4f}) -> {'adversary wins' if val > T + 1e-3 else 'REQUESTER wins'} [{time.time()-t0:.0f}s]", flush=True)
