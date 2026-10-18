"""Symbolic Kerr-Newman Einstein check in atom variables (r, k1, k2, k3), relation k1^2+k2^2+k3^2 = 1.
Mirrors the Lean definitions in Def_NoHair_coordinates.lean exactly (index conventions included)."""
import sympy as sp, time, pickle, sys

r, k1, k2, k3, a, m, e = sp.symbols('r k1 k2 k3 a m e')
ATOMS = [r, k1, k2, k3]
S = r**2 + a**2 * k3**2          # Sigma / r^2
Q = r**2 + a**2
x = r*k1 - a*k2
y = a*k1 + r*k2
z = r*k3

Dr = [0, x*r/S, y*r/S, k3*Q/S]
def dk1(i):
    if i == 0: return 0
    return (Dr[i]*x + (r if i == 1 else 0) + (a if i == 2 else 0)) / Q - k1*2*r*Dr[i]/Q
def dk2(i):
    if i == 0: return 0
    return (Dr[i]*y + (r if i == 2 else 0) - (a if i == 1 else 0)) / Q - k2*2*r*Dr[i]/Q
def dk3(i):
    if i == 0: return 0
    return (1/r if i == 3 else 0) - k3*Dr[i]/r
DATOM = {r: Dr, k1: [dk1(i) for i in range(4)], k2: [dk2(i) for i in range(4)], k3: [dk3(i) for i in range(4)]}

REL = k1**2 + k2**2 + k3**2 - 1

def red(expr):
    """Canonical form: cancel, reduce numerator mod REL (eliminate k1^2)."""
    expr = sp.cancel(sp.together(expr))
    num, den = sp.fraction(expr)
    num = sp.rem(sp.expand(num), REL, k1)
    num = sp.expand(num)
    return sp.cancel(num / den) if num != 0 else sp.Integer(0)

def D(i, expr):
    if i == 0: return sp.Integer(0)
    return sum(sp.diff(expr, at) * DATOM[at][i] for at in ATOMS)

def nterms(expr):
    num, den = sp.fraction(sp.together(expr))
    return len(sp.Add.make_args(sp.expand(num)))

if __name__ == '__main__':
    t0 = time.time()
    # sanity: D_i annihilates REL mod REL, and D_i of coordinates
    for i in range(1, 4):
        assert red(D(i, REL)) == 0, i
        for j, c in enumerate([x, y, z]):
            assert red(D(i, c) - (1 if i == j+1 else 0)) == 0, (i, j)
    print('derivation sanity ok', time.time()-t0)
    eta = sp.diag(-1, 1, 1, 1)
    kl = [sp.Integer(1), k1, k2, k3]
    ku = [-1, k1, k2, k3]
    f = (2*m*r - e**2) / S
    g = [[eta[i, j] + f*kl[i]*kl[j] for j in range(4)] for i in range(4)]
    gi = [[eta[i, j] - f*ku[i]*ku[j] for j in range(4)] for i in range(4)]
    # check inverse
    for i in range(4):
        for j in range(4):
            assert red(sum(g[i][l]*gi[l][j] for l in range(4)) - (1 if i == j else 0)) == 0
    print('inverse ok', time.time()-t0)
    dg = [[[red(D(c, g[i][j])) for c in range(4)] for j in range(4)] for i in range(4)]
    print('dg done', time.time()-t0, max(nterms(dg[i][j][c]) for i in range(4) for j in range(4) for c in range(4)))
    Gam = [[[None]*4 for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for j in range(4):
            for k in range(j, 4):
                v = red(sum(sp.Rational(1, 2)*gi[i][l]*(dg[l][k][j] + dg[l][j][k] - dg[j][k][l]) for l in range(4)))
                Gam[i][j][k] = Gam[i][k][j] = v
    print('Gamma done', time.time()-t0, 'max terms', max(nterms(Gam[i][j][k]) for i in range(4) for j in range(4) for k in range(4)))
    dGam = [[[[None]*4 for _ in range(4)] for _ in range(4)] for _ in range(4)]
    for i in range(4):
        for j in range(4):
            for k in range(j, 4):
                for c in range(4):
                    v = red(D(c, Gam[i][j][k]))
                    dGam[i][j][k][c] = dGam[i][k][j][c] = v
    print('dGamma done', time.time()-t0, 'max terms', max(nterms(dGam[i][j][k][c]) for i in range(4) for j in range(4) for k in range(4) for c in range(4)))
    def riem(rho, sig, mu, nu):
        return dGam[rho][nu][sig][mu] - dGam[rho][mu][sig][nu] + sum(Gam[rho][mu][l]*Gam[l][nu][sig] - Gam[rho][nu][l]*Gam[l][mu][sig] for l in range(4))
    Ric = [[None]*4 for _ in range(4)]
    for s_ in range(4):
        for n_ in range(4):
            Ric[s_][n_] = red(sum(riem(rh, s_, rh, n_) for rh in range(4)))
    print('Ricci done', time.time()-t0, 'max terms', max(nterms(Ric[i][j]) for i in range(4) for j in range(4)))
    Rs = red(sum(gi[i][j]*Ric[i][j] for i in range(4) for j in range(4)))
    print('scalar curvature', Rs)
    A = [e*r/S*kl[mu] for mu in range(4)]
    F = [[red(D(mu, A[nu]) - D(nu, A[mu])) for nu in range(4)] for mu in range(4)]
    FF = red(sum(F[al][be]*sum(gi[al][mu]*gi[be][nu]*F[mu][nu] for mu in range(4) for nu in range(4)) for al in range(4) for be in range(4)))
    ok = True
    T = [[None]*4 for _ in range(4)]
    for mu in range(4):
        for nu in range(4):
            T[mu][nu] = red(2*(sum(F[mu][al]*gi[al][be]*F[nu][be] for al in range(4) for be in range(4)) - sp.Rational(1, 4)*g[mu][nu]*FF))
            Ein = red(Ric[mu][nu] - sp.Rational(1, 2)*Rs*g[mu][nu])
            d = red(Ein - T[mu][nu])
            if d != 0:
                ok = False; print('MISMATCH', mu, nu, d)
    print('EINSTEIN OK' if ok else 'FAIL', time.time()-t0)
    pickle.dump({'Gam': Gam, 'dGam': dGam, 'Ric': Ric, 'Rs': Rs, 'F': F, 'T': T, 'FF': FF, 'dg': dg}, open('ks_atoms.pkl', 'wb'))
