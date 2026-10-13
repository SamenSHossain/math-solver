import sympy as sp, itertools
t,x,y,z=sp.symbols('t x y z',real=True); X=[t,x,y,z]
a,e,m=sp.Rational(3,7),sp.Rational(2,5),sp.Rational(11,10)
pt={t:0,x:sp.Rational(13,10),y:sp.Rational(-7,10),z:sp.Rational(9,10)}
rho2=x**2+y**2+z**2
r=sp.sqrt((rho2-a**2+sp.sqrt((rho2-a**2)**2+4*a**2*z**2))/2)
k=[sp.Integer(1),(r*x+a*y)/(r**2+a**2),(r*y-a*x)/(r**2+a**2),z/r]
f=r**2*(2*m*r-e**2)/(r**4+a**2*z**2)
H=e*r**3/(r**4+a**2*z**2); A=[H*ki for ki in k]
eta=sp.diag(-1,1,1,1)
g=[[eta[i,j]+f*k[i]*k[j] for j in range(4)] for i in range(4)]
P=40
N=lambda ex: sp.N(ex.subs(pt),P)
g0=sp.Matrix(4,4,lambda i,j:N(g[i][j]))
dg=[[[N(sp.diff(g[i][j],X[l])) for l in range(4)] for j in range(4)] for i in range(4)]
ddg={}
for i in range(4):
  for j in range(i,4):
    for l in range(4):
      for n in range(l,4):
        v=N(sp.diff(g[i][j],X[l],X[n])); 
        for (p,q) in [(i,j),(j,i)]:
          ddg[(p,q,l,n)]=v; ddg[(p,q,n,l)]=v
gi=g0.inv()
dgi=[None]*4
for l in range(4):
    D=sp.Matrix(4,4,lambda i,j:dg[i][j][l]); dgi[l]=-gi*D*gi
def Gam(i,j,kk): return sum(sp.Rational(1,2)*gi[i,l]*(dg[l][kk][j]+dg[l][j][kk]-dg[j][kk][l]) for l in range(4))
def dGam(i,j,kk,n):
    return sum(sp.Rational(1,2)*(dgi[n][i,l]*(dg[l][kk][j]+dg[l][j][kk]-dg[j][kk][l]) + gi[i,l]*(ddg[(l,kk,j,n)]+ddg[(l,j,kk,n)]-ddg[(j,kk,l,n)])) for l in range(4))
G=[[[Gam(i,j,kk) for kk in range(4)] for j in range(4)] for i in range(4)]
def riem(rh,s,mu,nu):
    return dGam(rh,nu,s,mu)-dGam(rh,mu,s,nu)+sum(G[rh][mu][l]*G[l][nu][s]-G[rh][nu][l]*G[l][mu][s] for l in range(4))
Ric=sp.Matrix(4,4,lambda s,nu: sum(riem(rh,s,rh,nu) for rh in range(4)))
Rs=sum(gi[s,n]*Ric[s,n] for s in range(4) for n in range(4))
Ein=Ric-sp.Rational(1,2)*Rs*g0
F=sp.Matrix(4,4,lambda i,j:N(sp.diff(A[j],X[i])-sp.diff(A[i],X[j])))
Fup=gi*F*gi.T
F2=sum(F[i,j]*Fup[i,j] for i in range(4) for j in range(4))
T=sp.Matrix(4,4,lambda mu,nu: 2*(sum(F[mu,al]*gi[al,be]*F[nu,be] for al in range(4) for be in range(4)) - sp.Rational(1,4)*g0[mu,nu]*F2))
print("max|Ein|:",max(abs(v) for v in Ein)); print("max|Ein-T|:",max(abs(v) for v in (Ein-T)))
print("Ein-T diag:",[sp.N(v,5) for v in (Ein-T).diagonal()])
