"""Extra symbolic checks for displayable formulas: compact form of d_j k_l, expansion/twist of the congruence,
and limits at the disc.  Zero test as in audit_sym2.py (rational parametrisation of {C=0, r>0})."""
import sympy as sp
from sympy import LeviCivita as eps

x, y, z, r, a, m, e, u, v = sp.symbols('x y z r a m e u v', real=True)
X = [x, y, z]
C = r**4 - (x**2 + y**2 + z**2 - a**2) * r**2 - a**2 * z**2
dr = [sp.cancel(-sp.diff(C, xi) / sp.diff(C, r)) for xi in X]
s = 1 + u**2 + v**2
K = [2 * u / s, 2 * v / s, (1 - u**2 - v**2) / s]
par = {x: r * K[0] - a * K[1], y: a * K[0] + r * K[1], z: r * K[2]}
D = lambda E, i: sp.diff(E, X[i]) + sp.diff(E, r) * dr[i]
vanishes = lambda E: sp.cancel(sp.together(E.subs(par))) == 0
k = [(r * x + a * y) / (r**2 + a**2), (r * y - a * x) / (r**2 + a**2), z / r]
W = r**2 / (r**4 + a**2 * z**2)
ok = all(vanishes(D(k[l], j) - W * (r * (sp.KroneckerDelta(j, l) - k[j] * k[l]) + a * k[2] * sum(eps(l, j, mm) * k[mm] for mm in range(3))))
         for j in range(3) for l in range(3))
print("d_j k_l = W [ r (delta_jl - k_j k_l) + a k3 eps_ljm k_m ]:", ok)
div = sum(D(k[j], j) for j in range(3))
curl = [D(k[2], 1) - D(k[1], 2), D(k[0], 2) - D(k[2], 0), D(k[1], 0) - D(k[0], 1)]
print("div k = 2 r W:", vanishes(div - 2 * r * W))
print("curl k = -2 a k3 W k:", all(vanishes(curl[i] + 2 * a * k[2] * W * k[i]) for i in range(3)))
H = e * r**3 / (r**4 + a**2 * z**2)
psi = e * a * z * r / (r**4 + a**2 * z**2)
kc = sum(k[i] * curl[i] for i in range(3))
print("H = (e/2) div k  and  psi = -(e/2) k.curl k:", vanishes(H - e * div / 2) and vanishes(psi + e * kc / 2))
# behaviour at the open disc: approach (x,y,0) with x^2+y^2 = rp2 < a^2 along z -> 0+
rp2, zz = sp.symbols('rho_perp2 zeta', positive=True)
rr = sp.sqrt(((rp2 + zz**2 - a**2) + sp.sqrt((rp2 + zz**2 - a**2)**2 + 4 * a**2 * zz**2)) / 2)
fz = rr**2 * (2 * m * rr - e**2) / (rr**4 + a**2 * zz**2)
print("lim_{z->0+} f at the open disc =", sp.simplify(sp.limit(fz.subs(a, sp.Rational(1)).subs(rp2, sp.Rational(1, 4)), zz, 0, '+')),
      "(a=1, x^2+y^2=1/4; expected -e^2/(a^2 - x^2 - y^2) = -4e^2/3)")
print("lim_{z->0+} k3 =", sp.limit((zz / rr).subs(a, 1).subs(rp2, sp.Rational(1, 4)), zz, 0, '+'), "(and the negative of this from below)")
