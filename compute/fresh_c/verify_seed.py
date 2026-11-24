"""Exact-rational check of the configuration that beats every fixed-priority Fano-template policy tested
(fano_steer.py): A_1 = A_4 = A_5 = X, A_2 = A_3 = A_6 = Y, X and Y of mass 1 meeting in O(1) points.
Checks D = all of X u Y (mass 2 > T) with exact Fractions and the realized family reported by the MILP."""
from fractions import Fraction as F
def mask(s): return sum(1 << (int(c) - 1) for c in s)
T = F(19, 25)
mass = {mask("145"): F(1), mask("236"): F(1)}
realized = [mask(s) for s in ["1", "12", "1456", "2", "23", "236", "3", "4", "5", "6", "145"]]
def inD(J):
    comp = 63 ^ J
    return any((K & comp) == comp for K in realized)
D = sum(m for J, m in mass.items() if inD(J))
print("mass(D) =", D, " T =", T, " adversary wins:", D > T)
for i in range(6):
    assert sum(m for J, m in mass.items() if (J >> i) & 1) == 1
