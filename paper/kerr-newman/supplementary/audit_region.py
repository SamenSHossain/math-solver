"""C: zero set of ksRadius (Lean: Real.sqrt, which returns 0 on negative input) and a CTC remark."""
import mpmath as mp
import random
mp.mp.dps = 50


def ksRadius(a, x, y, z):
    rho2 = x**2 + y**2 + z**2
    q = (rho2 - a**2 + mp.sqrt((rho2 - a**2)**2 + 4 * a**2 * z**2)) / 2
    return mp.sqrt(q) if q > 0 else mp.mpf(0)   # Real.sqrt q = 0 for q <= 0


random.seed(1)
bad = 0
for trial in range(20000):
    a = mp.mpf(random.choice([0, random.uniform(-2, 2)]))
    x, y = [mp.mpf(random.uniform(-2.5, 2.5)) for _ in range(2)]
    z = mp.mpf(random.choice([0, random.uniform(-2, 2)]))
    if random.random() < 0.1:
        x = y = z = mp.mpf(0)
    r = ksRadius(a, x, y, z)
    pred_zero = (x**2 + y**2 + z**2 <= a**2) and (a * z == 0)
    if (r == 0) != pred_zero:
        bad += 1
    if r > 0:
        # quartic and spheroid equation hold; sign of a irrelevant
        assert abs(r**4 - (x**2 + y**2 + z**2 - a**2) * r**2 - a**2 * z**2) < mp.mpf(10)**-40
        assert abs((x**2 + y**2) / (r**2 + a**2) + z**2 / r**2 - 1) < mp.mpf(10)**-40
        assert ksRadius(-a, x, y, z) == r
        if a == 0:
            assert abs(r - mp.sqrt(x**2 + y**2 + z**2)) < mp.mpf(10)**-45
print("zero-set characterisation mismatches:", bad)
# r -> 0 continuously approaching the open disc from above/below, k3 = z/r jumps
a = mp.mpf('0.8')
for zz in ['1e-3', '-1e-3', '1e-9', '-1e-9']:
    zz = mp.mpf(zz)
    r = ksRadius(a, mp.mpf('0.3'), mp.mpf('-0.4'), zz)
    print("z=%s r=%s k3=z/r=%s  (sqrt(1-(x^2+y^2)/a^2)=%s)" % (mp.nstr(zz, 3), mp.nstr(r, 8), mp.nstr(zz / r, 10), mp.nstr(mp.sqrt(1 - mp.mpf('0.25') / a**2), 10)))
# CTC remark: horizontal circle x^2+y^2 = r^2+a^2, z = 0, tangent d_phi; g(d_phi,d_phi) = (r^2+a^2) g_yy at (sqrt(r^2+a^2),0,0)
m, a, e = mp.mpf(1), mp.mpf('0.6'), mp.mpf('0.5')
for r in ['0.05', '0.1', '0.2']:
    r = mp.mpf(r)
    X = mp.sqrt(r**2 + a**2)
    k2 = (r * 0 - a * X) / (r**2 + a**2)
    f = r**2 * (2 * m * r - e**2) / r**4
    print("KN m=1,a=0.6,e=0.5: r=%s  g_yy at (sqrt(r^2+a^2),0,0) = %s" % (r, mp.nstr(1 + f * k2**2, 8)))
e = 0
r = mp.mpf('0.05'); X = mp.sqrt(r**2 + a**2); k2 = -a * X / (r**2 + a**2); f = (2 * m * r) / r**2
print("Kerr (e=0): r=0.05 g_yy =", mp.nstr(1 + f * k2**2, 8))
