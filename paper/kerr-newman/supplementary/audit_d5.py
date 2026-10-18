"""D5 (generic linear algebra): if k is eta-null, k# = eta k, g = eta + f k k^T, F antisymmetric with F k# = lambda k,
then g^{-1} F g^{-T} = eta F eta and sqrt|det g| = 1.  Symbolic, with a rational parametrisation of null k."""
import sympy as sp
u, v, f, lam = sp.symbols('u v f lambda')
s = 1 + u**2 + v**2
k = sp.Matrix([1, 2 * u / s, 2 * v / s, (1 - u**2 - v**2) / s])
eta = sp.diag(-1, 1, 1, 1)
ks = eta * k
g = eta + f * k * k.T
print("k null:", sp.simplify((k.T * eta * k)[0]) == 0)
print("det g = -1:", sp.simplify(g.det()) == -1)
gi = eta - f * ks * ks.T
print("g^-1 = eta - f k# k#^T:", sp.simplify(g * gi - sp.eye(4)) == sp.zeros(4))
Fs = sp.symbols('F01 F02 F03 F12 F13 F23')
idx = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
F = sp.zeros(4)
for sy, (i, j) in zip(Fs, idx):
    F[i, j] = sy
    F[j, i] = -sy
sol = sp.solve(list(F * ks - lam * k), list(Fs), dict=True)
print("alignment solution families:", len(sol), "; free parameters:", [p for p in Fs if all(p not in so for so in sol)])
for so in sol:
    Fa = F.subs(so)
    print("g^-1 F g^-T - eta F eta == 0:", sp.simplify(gi * Fa * gi.T - eta * Fa * eta) == sp.zeros(4))
    print("k#^T F k# == 0:", sp.simplify((ks.T * Fa * ks)[0]) == 0)
