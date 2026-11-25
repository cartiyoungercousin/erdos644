"""Asymptotic range of Theorem D (counting form). Normalise by k: omega = r/k, t = T/k, N = 1+omega+t.
g(omega,t) = N h((1+omega)/N) - (t+omega) h(omega/(t+omega)) - (1+omega) >= 0  =>  dim C_ev >= k+r  => rho_par <= r+1.
(The conditions dim >= T and dim >= (n+1)/2 are implied when t < 1+omega.)
Also: three disjoint parity-correct Omega_i (Prop. 9 input) by applying Theorem D on V, V-Om1, V-Om1-Om2:
needs g(omega, t - 2 omega') >= 0 where Om sizes <= r+1 (asymptotically omega' = omega)."""
from math import log2
def h(p): return 0.0 if p <= 0 or p >= 1 else -p*log2(p)-(1-p)*log2(1-p)
def g(w, t):
    N = 1+w+t; return N*h((1+w)/N) - (t+w)*h(w/(t+w)) - (1+w)
def thr(t):
    w = 0.0
    while g(w, t) >= 0 and w < 3: w += 1e-4
    return w
for t in (0.75, 0.78, 0.8, 0.85, 0.875):
    print(f't={t}: Theorem D holds for omega < {thr(t):.4f} (N < {1+t+thr(t):.4f})')
# region N < 11/6 : omega + eps < 1/12, t = 3/4 + eps
worst = min(g(w, 0.75+e) for e in [i/1000 for i in range(0, 84)] for w in [j/1000 for j in range(0, 84)] if w+e < 1/12)
print('min g over N<11/6 region:', round(worst, 4))
worst3 = min(g(w, 0.75+e-2*w) for e in [i/1000 for i in range(0, 84)] for w in [j/1000 for j in range(1, 84)] if w+e < 1/12)
print('min g for third Omega (ground set shrunk by 2(r+1)) over N<11/6:', round(worst3, 4))
