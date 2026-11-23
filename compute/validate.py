"""Validate the checker against results known from FKW99, then probe the open parity case k = 3."""
import sys
import time

from typefam import complete, parity, verify_witness


def report(fam, p=7):
    t0 = time.time()
    tau, tvec = fam.tau()
    w = fam.find_bad_tuple(p)
    dt = time.time() - t0
    if w is None:
        prop = f"HAS property ({p},2)"
    else:
        ok = verify_witness(fam, w, p)
        prop = f"FAILS ({p},2)  [witness independently verified: {ok}]"
    print(f"{fam.name:<16} n={fam.n:<3} r={fam.r:<3} tau={tau:<3} tau/r={tau / fam.r:.3f}  {prop}  ({dt:.1f}s)")
    sys.stdout.flush()
    return w


if __name__ == "__main__":
    print("== complete families: expect K_{7k-1}^(4k) has (7,2), K_{7k}^(4k) fails")
    for k in (1, 2, 3):
        report(complete(7 * k - 1, 4 * k))
        report(complete(7 * k, 4 * k))
    print("== parity family: expect k=2 fails, k>=4 has (7,2); k=3 unknown")
    for k in (2, 3, 4, 5):
        w = report(parity(k))
        if w is not None:
            print("   witness signature counts (block, signature-bits): count")
            for (b, s), c in sorted(w["m"].items()):
                print(f"     block {'XY'[b]}  sig {s:07b}  x{c}")
            print("   edge types:", w["edge_types"])
