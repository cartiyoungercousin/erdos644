"""Consistency check between cotypes.js (labelled leaves containing co-type {0,1,2}) and cotypes2.js (classes + aut):
expected leaves = sum over classes of (5040/aut) * (#distinct 3-sets among co-types) / 35.  Usage: py leafcheck.py file"""
import sys
from fractions import Fraction
tot = Fraction(0)
for line in open(sys.argv[1]):
    if not line.strip(): continue
    body, tail = line.split("|"); a = int(tail.split()[0].split("=")[1])
    trip = sum(1 for t in body.split() if bin(int(t.split(":")[0])).count("1") == 3)
    tot += Fraction(5040, a) * trip / 35
print(sys.argv[1], "expected labelled leaves with {0,1,2}:", tot)
