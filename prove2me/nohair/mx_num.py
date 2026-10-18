import sympy as sp
t,x,y,z,a,e,m=sp.symbols('t x y z a e m',real=True)
X=[t,x,y,z]
rho2=x**2+y**2+z**2
r=sp.sqrt((rho2-a**2+sp.sqrt((rho2-a**2)**2+4*a**2*z**2))/2)
k=[1,(r*x+a*y)/(r**2+a**2),(r*y-a*x)/(r**2+a**2),z/r]
H=sp.r3 = r**3*e/(r**4+a**2*z**2)
A=[H*ki for ki in k]
eta=sp.diag(-1,1,1,1)
f=r**2*(2*m*r-e**2)/(r**4+a**2*z**2)
F=sp.Matrix(4,4,lambda i,j: sp.diff(A[j],X[i])-sp.diff(A[i],X[j]))
ks=[-k[0],k[1],k[2],k[3]]  # eta k (contravariant)
vals={a:sp.Rational(3,7),e:sp.Rational(2,5),m:sp.Rational(11,10),x:sp.Rational(13,10),y:sp.Rational(-7,10),z:sp.Rational(9,10),t:0}
Fn=F.subs(vals).evalf(30)
ksn=[sp.N(sp.sympify(v).subs(vals),30) for v in ks]; kn=[sp.N(sp.sympify(v).subs(vals),30) for v in k]
v=[sum(Fn[al,be]*ksn[be] for be in range(4)) for al in range(4)]
print("F k^ =",v); print("ratio to k:",[v[i]/kn[i] for i in range(4)])
# flat Maxwell: d_mu (eta^{mu a} eta^{nu b} F_ab)
Fup=sp.Matrix(4,4,lambda i,j: eta[i,i]*eta[j,j]*F[i,j])
for nu in range(4):
    s=sum(sp.diff(Fup[mu,nu],X[mu]) for mu in range(4))
    print("flat div nu=",nu, sp.N(s.subs(vals),25))
# curved check: g, ginv, sqrt|det| F^{mu nu}
g=eta+f*sp.Matrix(4,4,lambda i,j:k[i]*k[j])
gn=g.subs(vals).evalf(30); print("det g =",gn.det())
