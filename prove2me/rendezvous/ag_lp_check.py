import itertools, numpy as np
from scipy.optimize import linprog
# vars: t0..t3, a0..a3 (f), c0..c3 (g); cases: 0:(+,+) a=2+c, 1:(+,-) a=2-c, 2:(-,+) -a=2+c, 3:(-,-) -a=2-c
N=12; T=lambda i:i; A=lambda i:4+i; C=lambda i:8+i
best=None
for perm in itertools.permutations(range(4)):
    Aub=[];bub=[]
    def le(coefs,b):
        row=np.zeros(N)
        for k,v in coefs: row[k]+=v
        Aub.append(row); bub.append(b)
    pos={p:k for k,p in enumerate(perm)}
    for i in range(4):
        for s in (1,-1):
            le([(A(i),s),(T(i),-1)],0); le([(C(i),s),(T(i),-1)],0)
        le([(T(i),-1)],0)
    for i in range(4):
        for j in range(4):
            if pos[i]<pos[j]:
                le([(T(i),1),(T(j),-1)],0)
                for s in (1,-1):
                    le([(A(i),s),(A(j),-s),(T(j),-1),(T(i),1)],0)
                    le([(C(i),s),(C(j),-s),(T(j),-1),(T(i),1)],0)
    Aeq=[];beq=[]
    def eq(coefs,b):
        row=np.zeros(N)
        for k,v in coefs: row[k]+=v
        Aeq.append(row); beq.append(b)
    eq([(A(0),1),(C(0),-1)],2); eq([(A(1),1),(C(1),1)],2); eq([(A(2),-1),(C(2),-1)],2); eq([(A(3),-1),(C(3),1)],2)
    c=np.zeros(N); c[:4]=1
    r=linprog(c,A_ub=np.array(Aub),b_ub=bub,A_eq=np.array(Aeq),b_eq=beq,bounds=[(None,None)]*N)
    if best is None or r.fun<best[0]: best=(r.fun,perm,r.x)
    print(perm, round(r.fun,6))
print('MIN',best[0],best[1])
