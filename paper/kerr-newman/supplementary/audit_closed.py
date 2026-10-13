"""Cross-check the Lean closed forms Gam (40 Christoffels) and RicA (10 Ricci components), parsed from
Def_NoHair_KerrNewmanEinstein_Base.lean, against an independent numerical evaluation from the verbatim platform
definitions (mpmath.diff, 60 digits).  RicA is compared with the numerically computed Ricci tensor."""
import os as _os
_HERE = _os.path.dirname(_os.path.abspath(__file__))
_NOHAIR = _os.path.normpath(_os.path.join(_HERE, '..', '..', '..', 'prove2me', 'nohair'))
import re
import mpmath as mp
import sympy as sp
from audit_num import ksRadius, ksNull, metric, potential, partial, unit, check
mp.mp.dps = 60
base = open(_os.path.join(_NOHAIR, 'einstein', 'Def_NoHair_KerrNewmanEinstein_Base.lean')).read()


def lean_to_py(s):
    s = re.sub(r'\(\s*(-?\d+)\s*:\s*ℕ\s*\)', r'\1', s)
    s = re.sub(r'\(\s*(-?\d+)\s*:\s*ℝ\s*\)', r'(\1)', s)
    return s.replace('^', '**').replace('![', '[')


def body(name):
    mt = re.search(r'noncomputable def ' + name + r' \(a m e R K1 K2 K3 W : ℝ\) : ℝ :=\s*(.*?)\n\n', base, re.S)
    return lean_to_py(mt.group(1))


def ev(name, env):
    return eval(body(name), {}, env)


cases = [("1.1", "0.43", "0.4", ("1.3", "-0.7", "0.9")), ("0.5", "1.2", "0.9", ("0.7", "1.1", "-0.4")),
         ("-0.8", "-0.7", "1.3", ("-0.2", "0.5", "0.6"))]
for m, a, e, p in cases:
    m, a, e = mp.mpf(m), mp.mpf(a), mp.mpf(e)
    p = tuple(mp.mpf(c) for c in p)
    r = ksRadius(a, *p)
    k = ksNull(a, *p)
    W = 1 / (r**2 + a**2 * k[3]**2)
    env = dict(a=a, m=m, e=e, R=r, K1=k[1], K2=k[2], K3=k[3], W=W)
    # numeric Christoffels
    N = range(4)
    g = mp.matrix(4, 4)
    dg = {}
    for i in N:
        for j in N:
            fun = lambda X, Y, Z, i=i, j=j: metric(m, a, e, X, Y, Z, i, j)
            g[i, j] = fun(*p)
            for l in N:
                dg[(i, j, l)] = partial(fun, p, unit(l))
    gi = g**-1
    errG = 0
    for i in N:
        for j in N:
            for kk in range(j, 4):
                num = sum(gi[i, l] * (dg[(l, kk, j)] + dg[(l, j, kk)] - dg[(j, kk, l)]) for l in N) / 2
                errG = max(errG, abs(num - ev(f"G{i}{j}{kk}", env)))
    # numeric Maxwell source (== Einstein tensor == Ricci, verified in audit_num); compare with RicA
    dA = {(i, l): partial(lambda X, Y, Z, i=i: potential(a, e, X, Y, Z, i), p, unit(l)) for i in N for l in N}
    F = [[dA[(nu, mu)] - dA[(mu, nu)] for nu in N] for mu in N]
    Fup = [[sum(gi[al, x] * gi[be, y] * F[x][y] for x in N for y in N) for be in N] for al in N]
    F2 = sum(F[al][be] * Fup[al][be] for al in N for be in N)
    T = [[2 * (sum(F[mu][al] * gi[al, be] * F[nu][be] for al in N for be in N) - g[mu, nu] * F2 / 4) for nu in N] for mu in N]
    errR = max(abs(T[i][j] - ev(f"Ric{i}{j}", env)) for i in N for j in range(i, 4))
    print(f"m={m} a={a} e={e}: max|Gamma_num - Gam_Lean| = {mp.nstr(errG, 3)},  max|T_num - RicA_Lean| = {mp.nstr(errR, 3)}")
