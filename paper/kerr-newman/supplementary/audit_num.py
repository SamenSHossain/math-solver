"""End-to-end numerical audit of EinsteinMaxwellAt for the platform definitions, transcribed verbatim:
ksRadius (nested sqrt formula), ksNull, ksProfile, kerrNewmanMetric, kerrNewmanPotential, kerrNewmanField,
christoffel (via matrix inverse), riemann/ricci/scalarCurvature/einsteinTensor, raiseBoth, maxwellSource,
and the curved Maxwell divergence  d_mu( sqrt|det g| F^{mu nu} ).
All partial derivatives (first and second) of the metric and potential are computed by mpmath.diff
(high-precision numerical differentiation) applied to the verbatim definitions; nothing uses the
atoms or any closed form.  t-derivatives are identically 0 since no definition depends on y 0.
"""
import mpmath as mp
import itertools, random

mp.mp.dps = 60


def ksRadius(a, x, y, z):
    rho2 = x**2 + y**2 + z**2
    q = (rho2 - a**2 + mp.sqrt((rho2 - a**2)**2 + 4 * a**2 * z**2)) / 2
    return mp.sqrt(q) if q > 0 else mp.mpf(0)


def ksNull(a, x, y, z):
    r = ksRadius(a, x, y, z)
    return [mp.mpf(1), (r * x + a * y) / (r**2 + a**2), (r * y - a * x) / (r**2 + a**2), z / r]


def ksProfile(m, a, e, x, y, z):
    r = ksRadius(a, x, y, z)
    return r**2 * (2 * m * r - e**2) / (r**4 + a**2 * z**2)


eta = [[-1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]


def metric(m, a, e, x, y, z, i, j):
    k = ksNull(a, x, y, z)
    return eta[i][j] + ksProfile(m, a, e, x, y, z) * k[i] * k[j]


def potential(a, e, x, y, z, i):
    r = ksRadius(a, x, y, z)
    return e * r**3 / (r**4 + a**2 * z**2) * ksNull(a, x, y, z)[i]


def partial(fun, p, orders):
    """orders: tuple over (t,x,y,z); t-derivative of a t-independent function is 0"""
    if orders[0] > 0:
        return mp.mpf(0)
    return mp.diff(lambda X, Y, Z: fun(X, Y, Z), p, orders[1:])


def unit(*idx):
    o = [0, 0, 0, 0]
    for i in idx:
        o[i] += 1
    return tuple(o)


def check(m, a, e, p):
    m, a, e = mp.mpf(m), mp.mpf(a), mp.mpf(e)
    p = tuple(mp.mpf(c) for c in p)
    r = ksRadius(a, *p)
    assert r > 0
    N = range(4)
    g = mp.matrix(4, 4)
    dg = {}
    ddg = {}
    for i in N:
        for j in range(i, 4):
            fun = lambda X, Y, Z, i=i, j=j: metric(m, a, e, X, Y, Z, i, j)
            g[i, j] = g[j, i] = fun(*p)
            for l in N:
                dg[(i, j, l)] = dg[(j, i, l)] = partial(fun, p, unit(l))
                for n in range(l, 4):
                    v = partial(fun, p, unit(l, n))
                    for (u, w) in [(i, j), (j, i)]:
                        ddg[(u, w, l, n)] = ddg[(u, w, n, l)] = v
    A = [potential(a, e, *p, i) for i in N]
    dA = {}
    ddA = {}
    for i in N:
        fun = lambda X, Y, Z, i=i: potential(a, e, X, Y, Z, i)
        for l in N:
            dA[(i, l)] = partial(fun, p, unit(l))
            for n in range(l, 4):
                ddA[(i, l, n)] = ddA[(i, n, l)] = partial(fun, p, unit(l, n))
    detg = mp.det(g)
    gi = g**-1
    dgi = []
    for l in N:
        Dl = mp.matrix(4, 4)
        for i in N:
            for j in N:
                Dl[i, j] = dg[(i, j, l)]
        dgi.append(-gi * Dl * gi)

    def Gam(i, j, k):
        return sum(mp.mpf(1) / 2 * gi[i, l] * (dg[(l, k, j)] + dg[(l, j, k)] - dg[(j, k, l)]) for l in N)

    def dGam(i, j, k, n):
        return sum(mp.mpf(1) / 2 * (dgi[n][i, l] * (dg[(l, k, j)] + dg[(l, j, k)] - dg[(j, k, l)])
                                    + gi[i, l] * (ddg[(l, k, j, n)] + ddg[(l, j, k, n)] - ddg[(j, k, l, n)])) for l in N)
    G = [[[Gam(i, j, k) for k in N] for j in N] for i in N]

    def riem(rh, s, mu, nu):
        return dGam(rh, nu, s, mu) - dGam(rh, mu, s, nu) + sum(G[rh][mu][l] * G[l][nu][s] - G[rh][nu][l] * G[l][mu][s] for l in N)
    Ric = [[sum(riem(rh, s, rh, nu) for rh in N) for nu in N] for s in N]
    Rs = sum(gi[s, nu] * Ric[s][nu] for s in N for nu in N)
    Ein = [[Ric[mu][nu] - Rs * g[mu, nu] / 2 for nu in N] for mu in N]
    # field F_{mu nu} = d_mu A_nu - d_nu A_mu
    F = [[dA[(nu, mu)] - dA[(mu, nu)] for nu in N] for mu in N]
    dF = {(mu, nu, l): ddA[(nu, mu, l)] - ddA[(mu, nu, l)] for mu in N for nu in N for l in N}
    Fup = [[sum(gi[al, mu] * gi[be, nu] * F[mu][nu] for mu in N for nu in N) for be in N] for al in N]
    F2 = sum(F[al][be] * Fup[al][be] for al in N for be in N)
    T = [[2 * (sum(F[mu][al] * gi[al, be] * F[nu][be] for al in N for be in N) - g[mu, nu] * F2 / 4) for nu in N] for mu in N]
    einres = max(abs(Ein[mu][nu] - T[mu][nu]) for mu in N for nu in N)
    einscale = max(abs(T[mu][nu]) for mu in N for nu in N)
    # Maxwell: d_mu (sqrt|det g| g^{mu al} g^{nu be} F_{al be}); det g is checked to be -1 numerically;
    # d sqrt|det g| = 1/2 sqrt|det g| g^{ab} d g_{ab}
    sq = mp.sqrt(abs(detg))
    dsq = [sq / 2 * sum(gi[i, j] * dg[(j, i, l)] for i in N for j in N) for l in N]
    div = []
    for nu in N:
        s = 0
        for mu in N:
            term = dsq[mu] * Fup[mu][nu]
            for al in N:
                for be in N:
                    term += sq * (dgi[mu][mu, al] * gi[nu, be] * F[al][be] + gi[mu, al] * dgi[mu][nu, be] * F[al][be]
                                  + gi[mu, al] * gi[nu, be] * dF[(al, be, mu)])
            s += term
        div.append(s)
    bianchi = max(abs(dF[(mu, nu, l)] + dF[(nu, l, mu)] + dF[(l, mu, nu)]) for l in N for mu in N for nu in N)
    trace = max(abs(sum(G[rh][rh][s] for rh in N)) for s in N)
    return dict(r=r, detg=detg, R=Rs, einres=einres, einscale=einscale, maxres=max(abs(v) for v in div),
                bianchi=bianchi, trGam=trace,
                Fscale=max(abs(F[i][j]) for i in N for j in N))


cases = [
    # (m, a, e, (x, y, z), comment)
    ("1.1", "0.43", "0.4", ("1.3", "-0.7", "0.9"), "sub-extremal, exterior"),
    ("1", "0.6", "0.5", ("0.3", "0.2", "0.25"), "sub-extremal, inside inner horizon r<r_-"),
    ("1", "0.6", "0.5", ("0.9", "-0.8", "0.5"), "sub-extremal, between horizons"),
    ("0.5", "1.2", "0.9", ("0.7", "1.1", "-0.4"), "naked: a^2+e^2>m^2"),
    ("-0.8", "-0.7", "1.3", ("-0.2", "0.5", "0.6"), "negative mass, negative a"),
    ("0.9", "0.8", "0.6", ("0.3", "-0.4", "0.001"), "just above the disc (x^2+y^2<a^2, z small)"),
    ("0.9", "0.8", "0.6", ("0.3", "-0.4", "-0.001"), "just below the disc"),
    ("0.9", "0", "0.6", ("0.3", "-0.4", "0.2"), "a=0: Reissner-Nordstrom"),
    ("0", "0", "0.7", ("1.2", "0.1", "-0.3"), "m=a=0, e!=0"),
    ("0.9", "0.8", "0", ("2.0", "0.5", "0.3"), "e=0: Kerr"),
]
if __name__ == "__main__":
    for m, a, e, p, c in cases:
        res = check(m, a, e, p)
        print(f"{c:45s} m={m} a={a} e={e} p={p}")
        print("    r=%s det g=%s R=%s" % (mp.nstr(res['r'], 12), mp.nstr(res['detg'], 25), mp.nstr(res['R'], 5)))
        print("    max|G-T|=%s (scale %s)  max|div|=%s (F scale %s)  bianchi=%s  trGam=%s" % (
            mp.nstr(res['einres'], 5), mp.nstr(res['einscale'], 5), mp.nstr(res['maxres'], 5),
            mp.nstr(res['Fscale'], 5), mp.nstr(res['bianchi'], 5), mp.nstr(res['trGam'], 5)), flush=True)
