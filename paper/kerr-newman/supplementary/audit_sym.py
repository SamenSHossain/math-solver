"""Independent symbolic audit of the Kerr-Newman Kerr-Schild formulas (items D1-D8).

Method: work with x, y, z and r as independent polynomial variables; r is the implicit
function defined by the quartic C(r,x,y,z) = r^4 - (rho^2 - a^2) r^2 - a^2 z^2 = 0.
Total derivative D_i E = dE/dx_i + dE/dr * r_i with r_i = -C_{x_i}/C_r (implicit function thm).
An expression E(x,y,z,r) is shown to vanish on {C = 0, r > 0} by: numerator of together(E),
pseudo-remainder modulo C (monic in r) == 0. Denominators are checked to be nonzero on r>0
by hand (they are products of r, r^2+a^2, r^4+a^2 z^2).
"""
import os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_NOHAIR = _os.path.normpath(_os.path.join(_HERE, '..', '..', '..', 'prove2me', 'nohair'))
import sympy as sp
import re, sys

x, y, z, r, a, m, e = sp.symbols('x y z r a m e', real=True)
X = [x, y, z]
rho2 = x**2 + y**2 + z**2
C = r**4 - (rho2 - a**2) * r**2 - a**2 * z**2

dr = [sp.simplify(-sp.diff(C, xi) / sp.diff(C, r)) for xi in X]


def D(E, i):
    """total spatial derivative d/dx_i (i=0,1,2 for x,y,z) with r = r(x,y,z)"""
    return sp.diff(E, X[i]) + sp.diff(E, r) * dr[i]


def vanishes(E):
    num = sp.numer(sp.together(sp.expand(E)))
    num = sp.expand(num)
    if num == 0:
        return True
    rem = sp.prem(num, C, r)
    return sp.expand(rem) == 0


def report(name, ok):
    print(f"[{'OK' if ok else 'FAIL'}] {name}")
    if not ok:
        sys.exit(1)


# ---- D1: partial derivatives of r -------------------------------------------------
den = r**4 + a**2 * z**2
W_xyz = r**2 / den                       # claim: W = r^2/(r^4+a^2 z^2)
report("dr/dx = r^3 x/(r^4+a^2 z^2)", vanishes(dr[0] - r**3 * x / den))
report("dr/dy = r^3 y/(r^4+a^2 z^2)", vanishes(dr[1] - r**3 * y / den))
report("dr/dz = r (r^2+a^2) z/(r^4+a^2 z^2)", vanishes(dr[2] - r * (r**2 + a**2) * z / den))

k1 = (r * x + a * y) / (r**2 + a**2)
k2 = (r * y - a * x) / (r**2 + a**2)
k3 = z / r
kk = [k1, k2, k3]
W = 1 / (r**2 + a**2 * k3**2)
report("W = 1/(r^2+a^2 k3^2) equals r^2/(r^4+a^2 z^2)", sp.simplify(W - W_xyz) == 0)
report("x = r k1 - a k2", sp.simplify(r * k1 - a * k2 - x) == 0)
report("y = a k1 + r k2", sp.simplify(a * k1 + r * k2 - y) == 0)
report("z = r k3", sp.simplify(r * k3 - z) == 0)
report("k1^2+k2^2+k3^2 = 1 on C=0", vanishes(k1**2 + k2**2 + k3**2 - 1))
f = r**2 * (2 * m * r - e**2) / den
H = e * r**3 / den
report("f = (2 m r - e^2) W", sp.simplify(f - (2 * m * r - e**2) * W) == 0)
report("H = e r W", sp.simplify(H - e * r * W) == 0)

# atom forms of dr (paper display)  dr_x = r W x = r W (r k1 - a k2), etc.
report("dr/dx = rW(r k1 - a k2)", vanishes(dr[0] - r * W * (r * k1 - a * k2)))
report("dr/dy = rW(a k1 + r k2)", vanishes(dr[1] - r * W * (a * k1 + r * k2)))
report("dr/dz = (r^2+a^2) k3 W", vanishes(dr[2] - (r**2 + a**2) * k3 * W))

# ---- compare with the Lean atom closed forms dRt, dKt, dWt, dfA, dHA --------------
R_, K1, K2, K3, Wsym = sp.symbols('R K1 K2 K3 W')
base = open(_os.path.join(_NOHAIR, 'einstein', 'Def_NoHair_KerrNewmanEinstein_Base.lean')).read()


def lean_to_py(s):
    s = re.sub(r'\(\s*(-?\d+)\s*:\s*ℕ\s*\)', r'\1', s)
    s = re.sub(r'\(\s*(-?\d+)\s*:\s*ℝ\s*\)', r'(\1)', s)
    s = s.replace('^', '**').replace('![', '[')
    return s


def lean_def(name):
    mt = re.search(r'noncomputable def ' + name + r' \([^)]*\)[^:]*: [^=]*:=\s*(.*?)\n\n', base, re.S)
    body = mt.group(1)
    body = body.split('\n/--')[0]
    return eval(lean_to_py(body), {'R': R_, 'K1': K1, 'K2': K2, 'K3': K3, 'W': Wsym, 'a': a, 'm': m, 'e': e})


atom_sub = {R_: r, K1: k1, K2: k2, K3: k3, Wsym: W}
dRt = lean_def('dRt')
dKt = lean_def('dKt')
dWt = lean_def('dWt')
dfA = lean_def('dfA')
dHA = lean_def('dHA')
for j in range(3):
    report(f"Lean dRt[{j+1}] = d_j r", vanishes(sp.sympify(dRt[j + 1]).subs(atom_sub) - dr[j]))
    report(f"Lean dWt[{j+1}] = d_j W", vanishes(sp.sympify(dWt[j + 1]).subs(atom_sub) - D(W, j)))
    report(f"Lean dfA[{j+1}] = d_j f", vanishes(sp.sympify(dfA[j + 1]).subs(atom_sub) - D(f, j)))
    report(f"Lean dHA[{j+1}] = d_j H", vanishes(sp.sympify(dHA[j + 1]).subs(atom_sub) - D(H, j)))
    for l in range(3):
        report(f"Lean dKt[{l+1}][{j+1}] = d_j k_l", vanishes(sp.sympify(dKt[l + 1][j + 1]).subs(atom_sub) - D(kk[l], j)))
for l in range(4):
    report(f"Lean dKt row/col 0 zero", all(sp.sympify(v) == 0 for v in [dKt[0][l], dKt[l][0]]))

# ---- D2: null, det, inverse --------------------------------------------------------
k = [sp.Integer(1), k1, k2, k3]
eta = sp.diag(-1, 1, 1, 1)
report("k null for eta: -k0^2+k1^2+k2^2+k3^2 = 0", vanishes(-1 + k1**2 + k2**2 + k3**2))
# generic algebra: det and inverse of eta + f k k^T for a null k (rational parametrisation of S^2)
u, v, fs = sp.symbols('u v f')
nk = [sp.Integer(1), 2 * u / (1 + u**2 + v**2), 2 * v / (1 + u**2 + v**2), (1 - u**2 - v**2) / (1 + u**2 + v**2)]
kv = sp.Matrix(nk)
g = eta + fs * kv * kv.T
ks = eta * kv
report("det(eta + f k k^T) = -1 for null k (generic f)", sp.simplify(g.det() + 1) == 0)
report("(eta + f k k^T)^{-1} = eta - f k# k#^T, k# = eta k", sp.simplify(g * (eta - fs * ks * ks.T) - sp.eye(4)) == sp.zeros(4))

# ---- D3: geodesic -------------------------------------------------------------------
# k#^nu d_nu k_mu with k#^0 = -1 and d_0 = 0 -> sum_i k_i d_i k_mu
for mu in range(3):
    report(f"geodesic: sum_i k_i d_i k_{mu+1} = 0", vanishes(sum(kk[i] * D(kk[mu], i) for i in range(3))))
for mu in range(3):
    report(f"sum_nu k#^nu d_mu k_nu = 0 (from nullity) mu={mu+1}", vanishes(sum(kk[i] * D(kk[i], mu) for i in range(3))))
report("k.grad r = 1 (r is an affine parameter along k)", vanishes(sum(kk[i] * D(r, i) for i in range(3)) - 1))
report("k.grad k3 = 0", vanishes(sum(kk[i] * D(k3, i) for i in range(3))))

print("D1-D3 symbolic checks passed (D4-D7: see audit_sym2.py, which uses a faster zero test; D5 generic algebra: audit_d5.py)")
