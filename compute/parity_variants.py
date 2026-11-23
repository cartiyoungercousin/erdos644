"""Vary the parity family: block sizes |X| = a, |Y| = b, uniformity r, parity of |A ∩ X|.

For each variant compute tau/r and whether (7,2) holds. Goal: see how far parity-type
families can push tau/r, and where they break.
"""
import sys
import time

from typefam import TypeFamily, verify_witness


def fam(a, b, r, parity_bit):
    return TypeFamily.from_predicate([a, b], r, lambda c: c[0] % 2 == parity_bit,
                                     name=f"X{a}Y{b}r{r}p{parity_bit}")


if __name__ == "__main__":
    r = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    best = []
    for n in range(r + 1, 2 * r):          # tau needs n > r
        for a in range(1, n):
            b = n - a
            for pb in (0, 1):
                try:
                    F = fam(a, b, r, pb)
                except ValueError:
                    continue
                tau, _ = F.tau()
                if tau / r <= 0.75:          # only interested in beating the complete family
                    continue
                t0 = time.time()
                w = F.find_bad_tuple(7)
                ok = w is None
                if ok:
                    best.append((tau / r, F.name, tau))
                print(f"{F.name:<16} tau={tau:<3} tau/r={tau / r:.3f} (7,2)={'YES' if ok else 'no '} ({time.time() - t0:.1f}s)",
                      flush=True)
    print("\nVariants with (7,2) and tau/r > 3/4:")
    for x in sorted(best, reverse=True):
        print("  ", x)
