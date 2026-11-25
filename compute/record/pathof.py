import sys
from fractions import Fraction as Fr
def path_of(p, level):
    lo = [Fr(0)]*3; hi = [Fr(1), Fr(1,2), Fr(1,2)]; s = ""
    for _ in range(level):
        o = 0
        for i in range(3):
            mid = (lo[i]+hi[i])/2
            if p[i] >= mid: o |= 1 << i; lo[i] = mid
            else: hi[i] = mid
        s += str(o)
    return s
if __name__ == "__main__":
    lev = int(sys.argv[1])
    print(",".join(path_of([Fr(v) for v in a.split(",")], lev) for a in sys.argv[2:]))
