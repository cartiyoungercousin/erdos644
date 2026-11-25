"""Independent referee code (verify_pen). Size conditions for Theorem PEN, written from the
hand proof only (not from compute/programme3).

Setting: H k-uniform on n points, every (k+r)-set contains a member, T = n-k-r >= 0.
Proof chain:
  pair x1,x2 with j=|x1^x2| <= k-hi: take A, |A cap x1| = l = k-hi, |A minus x1| = k+r-l  (needs 0<=l<=k, k+r-l <= n-k)
      -> member x2 subset A, j in [max(0,l-r), l]
  Lemma 5c needs |O| = k+r-2hi in [0, n-2k+j] for the realised j (worst j = max(0,l-r))
  then y with j' = |y cap xi| in I=[lo,hi]; pair bound on (xi,y) needs T >= j' if 2k-2j' <= k+r.
  weight <= r + |2j'-(k-r)| <= r + D(I).
"""
from math import ceil

def conds(n, k, r, lo, hi):
    """Exact sufficient conditions of the proof, for interval I=[lo,hi]. Returns list of failed names."""
    T = n - k - r
    bad = []
    w = hi - lo
    if not (2 * w + 2 > r): bad.append('2w+2>r')
    if lo < 0: bad.append('lo>=0')
    l = k - hi
    if not (0 <= l <= k): bad.append('0<=l<=k')
    if not (k + r - l <= n - k): bad.append('room_pair(hi<=T)')
    O = k + r - 2 * hi
    if O < 0: bad.append('O>=0')
    jmin = max(0, l - r)
    if not (O <= n - 2 * k + jmin): bad.append('room_O')
    # pair bound on (xi,y): need T >= j' when 2k-2j' <= k+r ; j' <= hi
    for jp in range(max(lo, 0), hi + 1):
        if 2 * k - 2 * jp <= k + r and jp > T:
            bad.append('T>=jprime'); break
        if 2 * k - 2 * jp > k + r:
            pass  # A subset of x1 ^ y needs |x1^y| >= k+r : true in this branch
    return bad

def D_of(k, r, lo, hi):
    return max(abs(2 * j - (k - r)) for j in range(lo, hi + 1))

def note_interval(k, r):
    """Interval prescribed by the note: w=ceil((r-1)/2), w+1 integers minimising D; ties -> lower interval."""
    w = ceil((r - 1) / 2) if r >= 1 else 0
    best = None
    for lo in range(-w - 2, k + 1):
        hi = lo + w
        D = D_of(k, r, lo, hi)
        if best is None or D < best[0]:
            best = (D, lo, hi)
    return best  # (D, lo, hi)

def pen_ok(n, k, r, P=None, any_interval=False):
    """Does the proof deliver a pencil of weight <= P (default floor(3r/2)+1)?"""
    if P is None: P = (3 * r) // 2 + 1
    if not any_interval:
        D, lo, hi = note_interval(k, r)
        # also try the other tie
        cands = [(lo, hi)]
        for lo2 in range(0, k + 1):
            hi2 = lo2 + (hi - lo)
            if D_of(k, r, lo2, hi2) == D and (lo2, hi2) != (lo, hi): cands.append((lo2, hi2))
        for (a, b) in cands:
            if r + D <= P and not conds(n, k, r, a, b): return True, (a, b, r + D)
        return False, (lo, hi, r + D, conds(n, k, r, lo, hi))
    for w in range(0, k + 1):
        if 2 * w + 2 <= r: continue
        for lo in range(0, k + 1):
            hi = lo + w
            if r + D_of(k, r, lo, hi) <= P and not conds(n, k, r, lo, hi):
                return True, (lo, hi, r + D_of(k, r, lo, hi))
    return False, None
