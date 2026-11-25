"""Which (W,d)-complete blocks are fatal for a k-uniform family H with tau(H) = T+1, T = ceil((3/4+eps)k)?
Exact integer conditions (no floats except the printed ratios).

  NC   (paper Thm NC, VERIFIED): w >= k+d+2 and T+1 > (k+1)/2 + max(0, 2k+2d+3-w).
  NCP  (relative pencil lemma, PROGRAMME5_COMPRESS Sec 2): Thm pen applied to the k-uniform family H[W] on ground set
       W (VERIFIED size conditions 4(w-k-d) >= 2k+5d+3, 3d <= 2k-2) gives a pencil of weight <= d+D; Lemma P1 with the
       AMBIENT T kills it iff d+D <= 4T-3k-6.
  NCP2 same with the two-stage size conditions of PROGRAMME5_BULK Thm 2S [hand]: 4(w-k-d) >= 2k+3d+3, 3 <= d <= 2k-4.
  NCFW Thm FW applied to H[W]: C(w,k) > C(k+d,d) C(w,p-1), p least prime >= (k+d+1)/2, p <= k; weight 2p-k.
For each eps and w/k: the largest fatal excess d, and the least fatal block transversal number tau_W = w-k-d+1
reported as (tau_W - 3k/4)/k.  Usage: py -3.14 ncp_region.py K"""
import sys, math
from fractions import Fraction as F

def D_of(k, d):
    w_ = max(0, -(-(d - 1) // 2))          # ceil((d-1)/2), >= 0
    return w_ if (w_ - (k + d)) % 2 == 0 else w_ + 1

def nc(k, T, w, d):
    a = max(0, 2 * k + 2 * d + 3 - w)
    return w >= k + d + 2 and 2 * (T + 1) > (k + 1) + 2 * a

def ncp(k, T, w, d, two_stage=False):
    Tw = w - k - d
    if two_stage:
        if not (3 <= d <= 2 * k - 4 and 4 * Tw >= 2 * k + 3 * d + 3): return False
    else:
        if not (d >= 0 and 3 * d <= 2 * k - 2 and 4 * Tw >= 2 * k + 5 * d + 3): return False
    return d + D_of(k, d) <= 4 * T - 3 * k - 6

def is_prime(m):
    if m < 2: return False
    i = 2
    while i * i <= m:
        if m % i == 0: return False
        i += 1
    return True

def ncfw(k, T, w, d):
    p = (k + d + 2) // 2                    # ceil((k+d+1)/2)
    while not is_prime(p): p += 1
    if p > k or w < 2 * k: pass
    if p > k: return False
    if 2 * p - k > 4 * T - 3 * k - 6: return False
    return math.comb(w, k) > math.comb(k + d, d) * math.comb(w, p - 1)

def dmax(test, k, T, w):
    best = None
    for d in range(0, 2 * k):
        if test(k, T, w, d): best = d
    return best

def main(K):
    k = K
    print('k = %d' % k)
    print('eps   w/k   | d_max: NC  NCP  NCP2  NCFW | least fatal (tau_W-3k/4)/k: NC  NCP  NCP2  NCFW')
    for eps in (F(1, 100), F(1, 44), F(1, 20), F(1, 10)):
        T = -(-(3 * k + 4 * eps * k) // 4) if False else math.ceil((F(3, 4) + eps) * k)
        for wr in (F(3, 2), F(8, 5), F(13, 8), F(5, 3), F(7, 4), F(11, 6), F(2), F(9, 4), F(5, 2)):
            w = int(wr * k)
            row = []
            for t in (nc, ncp, lambda a, b, c, e: ncp(a, b, c, e, True), ncfw):
                row.append(dmax(t, k, T, w))
            fat = ['   - ' if dm is None else '%+.3f' % ((w - k - dm + 1 - 0.75 * k) / k) for dm in row]
            print('%.3f %.3f | %s | %s' % (float(eps), float(wr), ' '.join('%4s' % ('-' if x is None else x) for x in row),
                                          ' '.join(fat)))
        print()

if __name__ == '__main__':
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 400)
