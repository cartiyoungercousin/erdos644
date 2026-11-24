"""Explicit Fano-template requester policies (mandatory blocks first, then extras by a priority rule);
adversary's exact best response via endgame.solve(mode='adv_free')."""
import sys, time
from endgame import solve, popc, tstr
def mask(s): return sum(1 << (int(c) - 1) for c in s)
LAB = {
 "pairs(14)(25)(36) lines 123,156,246,345": (["14", "25", "36"], ["123", "156", "246", "345"]),
 "pairs(14)(25)(36) lines 456,234,135,126": (["14", "25", "36"], ["456", "234", "135", "126"]),
 "pairs(12)(34)(56) lines 135,146,236,245": (["12", "34", "56"], ["135", "146", "236", "245"]),
 "pairs(12)(34)(56) lines 136,145,235,246": (["12", "34", "56"], ["136", "145", "235", "246"]),
}
def make_order(pairs, lines, extras):
    pm = [mask(p) for p in pairs]; lm = [mask(l) for l in lines]
    def order(i, types):
        b = 1 << i
        partner = 0
        for p in pm:
            if p & b: partner = p ^ b
        def mand(J): return any((l & b) and ((l ^ b) & J) == (l ^ b) for l in lm)
        def haspair(J): return any((p & J) == p for p in pm)
        if extras == "deg":
            key = lambda J: (not mand(J), -popc(J), J)
        elif extras == "partner":
            key = lambda J: (not mand(J), not (J & partner), -popc(J), J)
        elif extras == "pairtypes":   # mandatory, then types already containing a full pair, then partner, then degree
            key = lambda J: (not mand(J), not haspair(J), not (J & partner), -popc(J), J)
        return sorted(types, key=key)
    return order
if __name__ == "__main__":
    for T in [float(x) for x in sys.argv[1:]]:
        best = None
        for name, (pairs, lines) in LAB.items():
            for ex in ("deg", "partner", "pairtypes"):
                st, val, info = solve(T, "adv_free", req_order=make_order(pairs, lines, ex), tl=120)
                print(f"T={T} [{name} | extras={ex}]: max mass(D)={val:.4f} -> {'adversary wins' if val > T + 1e-3 else 'REQUESTER wins'}", flush=True)
                if best is None or val < best[0]: best = (val, name, ex, info)
        val, name, ex, info = best
        print(f"== T={T}: best policy [{name} | {ex}] adversary reaches mass(D)={val:.4f}")
        print("   final:", info["final"]); print("   realized:", info["realized"])
        for i, h in enumerate(info["hist"], start=2):
            print(f"   edge {i}: request {h['req']}  take {h['take']} fresh {h['fresh']}")
