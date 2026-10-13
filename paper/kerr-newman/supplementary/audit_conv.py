"""A: curvature conventions (exact transcription of the Lean definitions, dimension-generic),
D8: Groebner basis claim.  Symbolic (SymPy)."""
import sympy as sp


def geometry(g, X):
    n = len(X)
    gi = g.inv()
    # christoffel G y i j k = sum_l 1/2 g^{il} (d_j g_{lk} + d_k g_{lj} - d_l g_{jk})
    Gam = [[[sp.simplify(sum(sp.Rational(1, 2) * gi[i, l] * (sp.diff(g[l, k], X[j]) + sp.diff(g[l, j], X[k]) - sp.diff(g[j, k], X[l]))
                             for l in range(n))) for k in range(n)] for j in range(n)] for i in range(n)]

    # riemann rho sigma mu nu = d_mu Gam^rho_{nu sigma} - d_nu Gam^rho_{mu sigma}
    #                           + sum_l (Gam^rho_{mu l} Gam^l_{nu sigma} - Gam^rho_{nu l} Gam^l_{mu sigma})
    def riem(rh, s, mu, nu):
        return (sp.diff(Gam[rh][nu][s], X[mu]) - sp.diff(Gam[rh][mu][s], X[nu])
                + sum(Gam[rh][mu][l] * Gam[l][nu][s] - Gam[rh][nu][l] * Gam[l][mu][s] for l in range(n)))
    # ricci sigma nu = sum_rho riemann rho sigma rho nu
    Ric = sp.Matrix(n, n, lambda s, nu: sp.simplify(sum(riem(rh, s, rh, nu) for rh in range(n))))
    Rs = sp.simplify(sum(gi[s, nu] * Ric[s, nu] for s in range(n) for nu in range(n)))
    return Gam, riem, Ric, Rs


R0, th, ph = sp.symbols('R theta phi', positive=True)
g2 = sp.diag(R0**2, R0**2 * sp.sin(th)**2)
_, riem2, Ric2, Rs2 = geometry(g2, [th, ph])
print("2-sphere radius R: R^theta_{phi theta phi} =", sp.simplify(riem2(0, 1, 0, 1)), "; Ricci =", Ric2.tolist(), "; scalar =", Rs2)

# 3-sphere (positive), and hyperbolic plane (negative) for good measure
chi = sp.symbols('chi', positive=True)
g3 = sp.diag(1, sp.sin(chi)**2, sp.sin(chi)**2 * sp.sin(th)**2)
print("unit 3-sphere scalar =", geometry(g3, [chi, th, ph])[3])
yv, xv = sp.symbols('yv xv', positive=True)
print("hyperbolic plane (dx^2+dy^2)/y^2 scalar =", geometry(sp.diag(1 / yv**2, 1 / yv**2), [xv, yv])[3])

# Reissner-Nordstrom in Schwarzschild coords: verify G = 2(F F - 1/4 g F^2) with A = -(Q/r) dt and with the
# platform normalisation, using exactly the platform formulas.  Also check sign: f(r) = 1 - 2M/r + Q^2/r^2.
t, rr = sp.symbols('t r', positive=True)
M, Q = sp.symbols('M Q', real=True)
fr = 1 - 2 * M / rr + Q**2 / rr**2
X = [t, rr, th, ph]
g4 = sp.diag(-fr, 1 / fr, rr**2, rr**2 * sp.sin(th)**2)
Gam4, riem4, Ric4, Rs4 = geometry(g4, X)
Ein = sp.simplify(Ric4 - sp.Rational(1, 2) * Rs4 * g4)
Apot = [-Q / rr, 0, 0, 0]
F = sp.Matrix(4, 4, lambda i, j: sp.diff(Apot[j], X[i]) - sp.diff(Apot[i], X[j]))
gi = g4.inv()
Fup = gi * F * gi.T
F2 = sum(F[i, j] * Fup[i, j] for i in range(4) for j in range(4))
T = sp.Matrix(4, 4, lambda mu, nu: 2 * (sum(F[mu, al] * gi[al, be] * F[nu, be] for al in range(4) for be in range(4))
                                         - sp.Rational(1, 4) * g4[mu, nu] * F2))
print("RN (Schwarzschild coords): Einstein - maxwellSource =", sp.simplify(Ein - T) == sp.zeros(4), "; R =", Rs4)
print("RN: 8pi T_tt/... energy density check: maxwellSource_tt/(8pi) * (1/-g_tt) =", sp.simplify(T[0, 0] / (8 * sp.pi) / fr), "(should be Q^2/(8 pi r^4) > 0)")
print("RN: E_r = F_{r t} =", F[1, 0], " (outward for Q>0: charge = Q when A_t = -Q/r)")

# ---- D8: Groebner basis --------------------------------------------------------------
W, k1, r, k2, k3, a, m, e = sp.symbols('W k1 r k2 k3 a m e')
REL = k1**2 + k2**2 + k3**2 - 1
WREL = W * (r**2 + a**2 * k3**2) - 1
gens = (W, k1, r, k2, k3, a, m, e)
GB = sp.groebner([REL, WREL], *gens, order='lex')
print("lex GB:", GB.exprs)
print("LM(REL) =", sp.LM(REL, *gens, order='lex'), " LM(WREL) =", sp.LM(WREL, *gens, order='lex'))
print("is {REL, WREL} the reduced GB?", set(sp.expand(p) for p in GB.exprs) == {sp.expand(REL), sp.expand(WREL)})
# S-polynomial reduces to 0
S = sp.expand(sp.LT(WREL, *gens, order='lex') * REL - sp.LT(REL, *gens, order='lex') * WREL)  # lcm/LT trick with LT coprime
q, rem = sp.reduced(S, [REL, WREL], *gens, order='lex')
print("S-poly remainder:", rem)
