"""Faster symbolic verification of D4-D6 (alignment, flat Maxwell, Appell) and D7 (Christoffel trace).
Derivatives: chain rule with the implicit r (r_i = -C_{x_i}/C_r), exactly as in audit_sym.py.
Zero test: substitute the rational parametrisation of the variety {C = 0, r > 0}:
   k = (2u, 2v, 1-u^2-v^2)/(1+u^2+v^2),  x = r k1 - a k2,  y = a k1 + r k2,  z = r k3,
which maps (r>0, u, v) diffeomorphically onto an open dense subset of the r>0 sheet; a rational function of
(x,y,z,r) vanishes on {C=0, r>0} iff its pull-back is the zero rational function in (r,u,v,a,m,e)."""
import sympy as sp
import sys, time

x, y, z, r, a, m, e, u, v = sp.symbols('x y z r a m e u v', real=True)
X = [x, y, z]
C = r**4 - (x**2 + y**2 + z**2 - a**2) * r**2 - a**2 * z**2
dr = [sp.cancel(-sp.diff(C, xi) / sp.diff(C, r)) for xi in X]
s = 1 + u**2 + v**2
K = [2 * u / s, 2 * v / s, (1 - u**2 - v**2) / s]
par = {x: r * K[0] - a * K[1], y: a * K[0] + r * K[1], z: r * K[2]}
print("C vanishes on parametrisation:", sp.cancel(C.subs(par)) == 0)


def D(E, i):
    return sp.diff(E, X[i]) + sp.diff(E, r) * dr[i]


def vanishes(E):
    return sp.cancel(sp.together(E.subs(par))) == 0


def report(name, ok):
    print(f"[{'OK' if ok else 'FAIL'}] {name}", flush=True)
    if not ok:
        sys.exit(1)


den = r**4 + a**2 * z**2
k1 = (r * x + a * y) / (r**2 + a**2)
k2 = (r * y - a * x) / (r**2 + a**2)
k3 = z / r
k = [sp.Integer(1), k1, k2, k3]
ksh = [-1, k1, k2, k3]
W = r**2 / den
H = e * r**3 / den
f = r**2 * (2 * m * r - e**2) / den


def dmu(E, mu):
    return sp.Integer(0) if mu == 0 else D(E, mu - 1)


A = [H * ki for ki in k]
F = [[dmu(A[nu], mu) - dmu(A[mu], nu) for nu in range(4)] for mu in range(4)]
lam = -sum(dmu(H, nu) * ksh[nu] for nu in range(4))
for mu in range(4):
    report(f"sum_nu F_[{mu} nu] k#^nu = lambda k_{mu},  lambda := -k#^nu d_nu H",
           vanishes(sum(F[mu][nu] * ksh[nu] for nu in range(4)) - lam * k[mu]))
report("lambda = e (r^2 - a^2 k3^2) W^2  [W = 1/(r^2+a^2 k3^2)]", vanishes(lam - e * (r**2 - a**2 * k3**2) / (r**2 + a**2 * k3**2)**2))

# D6 flat Maxwell
t0 = time.time()
report("Delta H = 0", vanishes(sum(D(D(H, i), i) for i in range(3))))
psi = e * a * z * r / den
Av = [H * k1, H * k2, H * k3]
curl = [D(Av[2], 1) - D(Av[1], 2), D(Av[0], 2) - D(Av[2], 0), D(Av[1], 0) - D(Av[0], 1)]
for i in range(3):
    report(f"(curl A)_{i+1} = d_{i+1} psi,  psi = e a z r/(r^4+a^2 z^2)", vanishes(curl[i] - D(psi, i)))
report("Delta psi = 0", vanishes(sum(D(D(psi, i), i) for i in range(3))))
report("F_12 = d_z psi, F_23 = d_x psi, F_31 = d_y psi",
       vanishes(F[1][2] - D(psi, 2)) and vanishes(F[2][3] - D(psi, 0)) and vanishes(F[3][1] - D(psi, 1)))
report("F_i0 = d_i H", all(vanishes(F[i + 1][0] - D(H, i)) for i in range(3)))
I = sp.I
report("H + i psi = e/(r - i a z/r)", sp.simplify(H + I * psi - e / (r - I * a * z / r)) == 0)
report("(r - i a z/r)^2 = x^2 + y^2 + (z - i a)^2 on the variety",
       vanishes(sp.expand((r - I * a * z / r)**2 - (x**2 + y**2 + (z - I * a)**2))))
print("   time for D6:", round(time.time() - t0, 1), "s")

# D7: Christoffel trace = 1/2 d log|det g| = 0, from the metric directly (generic formula with g^-1 = eta - f k# k#^T)
eta = sp.diag(-1, 1, 1, 1)
g = sp.Matrix(4, 4, lambda i, j: eta[i, j] + f * k[i] * k[j])
gi = sp.Matrix(4, 4, lambda i, j: eta[i, j] - f * ksh[i] * ksh[j])
report("g * (eta - f k# k#^T) = 1 on the variety", all(vanishes(c) for c in (g * gi - sp.eye(4))))
for sg in range(4):
    tr = sum(sp.Rational(1, 2) * gi[i, l] * dmu(g[l, i], sg) for i in range(4) for l in range(4))
    report(f"sum_rho Gamma^rho_(rho {sg}) = 1/2 g^(il) d_{sg} g_(li) = 0", vanishes(tr))
print("all D4-D7 checks passed")
