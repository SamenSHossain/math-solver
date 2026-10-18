import numpy as np, itertools, math
perms=list(itertools.permutations(range(4)))
def phi(P,q):
    # sum_pi prod P^q  divided by uniform value
    s=0.0
    for pi in perms:
        s+=np.prod([P[i,pi[i]]**q for i in range(4)])
    return s/(24*0.25**(4*q))
def minor_perm(Pq,i,j):
    rows=[r for r in range(4) if r!=i]; cols=[c for c in range(4) if c!=j]
    M=Pq[np.ix_(rows,cols)]
    return sum(np.prod([M[a,s[a]] for a in range(3)]) for s in itertools.permutations(range(3)))
def best(q,trials=3000,seed=0):
    rng=np.random.default_rng(seed); r=1/(1-q); bestv=0; bestP=None
    for t in range(trials):
        P=rng.dirichlet(np.ones(4)*rng.choice([0.1,0.3,1,3]),size=4)
        for it in range(200):
            for i in range(4):
                Pq=P**q
                c=np.array([minor_perm(Pq,i,j) for j in range(4)])
                if c.max()<=0: continue
                x=c**r; P[i]=x/x.sum()
        v=phi(P,q)
        if v>bestv: bestv=v; bestP=P.copy()
    return bestv,bestP
for p in [1.70,1.7446,1.76,1.8,1.9,1.95,2.0]:
    v,P=best(1/p,trials=400)
    print(f"p={p}: max ratio {v:.6f}"); 
    if v>1+1e-9: print(np.round(P,4))
print("identity threshold", 4*math.log(4)/math.log(24))
