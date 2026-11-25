r"""Task 3(1') check for the copy-deletion step [computed exact]: for each x in X, the Y-triples of the kept (9,3)
members of F1 that avoid x must be ALL C(10,3) = 120 triples (then any Y-set meeting them has >= 8 points, and a
private set of a duplicate copy (X - x) + f would need >= 8 + 1 + 1 = 10 > 9 points).  Usage: py -3.14 copy_check.py"""
import numpy as np
F = [int(b) for b in np.load('out/fkwmin_random_1.npy')]; Xm = (1 << 12) - 1
for x in range(12):
    tri = set(B >> 12 for B in F if bin(B & Xm).count('1') == 9 and not B >> x & 1)
    print(x, len(tri), end='; ')
print()
