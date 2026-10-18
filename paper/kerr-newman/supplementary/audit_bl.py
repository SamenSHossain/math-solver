"""B: relate the platform Kerr-Schild metric/potential to Boyer-Lindquist Kerr-Newman (symbolic).
Spheroidal parametrisation x + i y = (r + i a) sin(th) e^{i ph}, z = r cos(th)."""
import sympy as sp

t, r, th, ph, a, m, e = sp.symbols('t r theta phi a m e', real=True)
x = (r * sp.cos(ph) - a * sp.sin(ph)) * sp.sin(th)
y = (r * sp.sin(ph) + a * sp.cos(ph)) * sp.sin(th)
z = r * sp.cos(th)
print("(x^2+y^2)/(r^2+a^2) + z^2/r^2 =", sp.simplify((x**2 + y**2) / (r**2 + a**2) + z**2 / r**2))
k = [sp.Integer(1), sp.simplify((r * x + a * y) / (r**2 + a**2)), sp.simplify((r * y - a * x) / (r**2 + a**2)), sp.simplify(z / r)]
print("k in spheroidal coords:", k)
f = sp.simplify(r**2 * (2 * m * r - e**2) / (r**4 + a**2 * z**2))
H = sp.simplify(e * r**3 / (r**4 + a**2 * z**2))
print("f =", f, "   H =", H)
eta = sp.diag(-1, 1, 1, 1)
g = sp.Matrix(4, 4, lambda i, j: eta[i, j] + f * k[i] * k[j])
U = [t, r, th, ph]
Xc = [t, x, y, z]
J = sp.Matrix(4, 4, lambda mu, a_: sp.diff(Xc[mu], U[a_]))
gs = sp.simplify(J.T * g * J)
ks = sp.simplify(J.T * sp.Matrix(k))       # pulled-back covector k
print("pulled-back k = ", list(ks))
Sig = r**2 + a**2 * sp.cos(th)**2
Delta = r**2 - 2 * m * r + a**2 + e**2
# Boyer-Lindquist: t = tB + T(r), ph = phB + P(r), T' = (r^2+a^2)/Delta - 1, P' = a/Delta
Jb = sp.eye(4)
Jb[0, 1] = (r**2 + a**2) / Delta - 1
Jb[3, 1] = a / Delta
gBL = sp.simplify(Jb.T * gs * Jb)
gstd = sp.zeros(4)
gstd[0, 0] = -(1 - (2 * m * r - e**2) / Sig)
gstd[0, 3] = gstd[3, 0] = -a * sp.sin(th)**2 * (2 * m * r - e**2) / Sig
gstd[1, 1] = Sig / Delta
gstd[2, 2] = Sig
gstd[3, 3] = (r**2 + a**2 + a**2 * sp.sin(th)**2 * (2 * m * r - e**2) / Sig) * sp.sin(th)**2
print("g_KS pulled back + BL shift == standard BL Kerr-Newman (Delta = r^2-2mr+a^2+e^2)?",
      sp.simplify(gBL - gstd) == sp.zeros(4))
A = sp.Matrix([H * kk for kk in k])
ABL = sp.simplify((J * Jb).T * A)
print("A in BL coords (t, r, th, ph):", [sp.simplify(c) for c in ABL])
print("A_t - e r/Sigma =", sp.simplify(ABL[0] - e * r / Sig), "; A_ph + a sin^2 e r/Sigma =",
      sp.simplify(ABL[3] + a * sp.sin(th)**2 * e * r / Sig), "; A_r =", sp.simplify(ABL[1]), "; A_th =", ABL[2])
# ingoing check for a = 0: k = dt + dr (+ angular terms vanish)
print("a=0 pulled-back k:", [sp.simplify(c.subs(a, 0)) for c in ks])
# frame dragging and asymptotic angular momentum
omega = sp.simplify(-gstd[0, 3] / gstd[3, 3])
print("frame-dragging omega = -g_tph/g_phph =", omega, "; large-r:", sp.limit(omega * r**3, r, sp.oo))
