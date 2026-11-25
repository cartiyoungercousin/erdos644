"""PETAL §41.4: re-check the 4-class union of arenas where Phi exceeds the arena form tau + (8/3)d.
Branch (a) alone (t large switches branch (b) off), and the full Phi at t = 3/4."""
import numpy as np
from multiarena import atoms, evaluate
AT = atoms(4)
s = np.array([0.0, 0.007386074923232649, 0.0, 0.004683050145881914, 0.0, 0.0, 0.012362372795376478, 0.015508281314776124,
              0.05866547281187389, 0.04703272213471724, 0.0, 0.03137483807322389, 0.03166880677257613, 0.0, 1.2481293844970474])
rho = np.array([0.03910729664412106, 0.016870794390112482, 0.02521763658147612, 0.004904422528792273])
e = evaluate(s, rho, 0.75, AT, 4); ea = evaluate(s, rho, 5.0, AT, 4)
af = e['tau'] + 8 * e['d'] / 3
print('c %.5f tau %.5f d %.5f | Phi(3/4) %.5f | branch (a) only %.5f | arena form %.5f | excess %.5f = %.3f d | SL1 margin %.4f'
      % (e['c'], e['tau'], e['d'], e['phi'], ea['phi'], af, ea['phi'] - af, (ea['phi'] - af) / e['d'], 0.75 - e['phi']))
