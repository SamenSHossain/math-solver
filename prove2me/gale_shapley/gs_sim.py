import itertools, random
def gs(n, manRank, womanRank):
    # manRank[m][w] = position; womanRank[w][m]
    manInv=[{manRank[m][w]:w for w in range(n)} for m in range(n)]
    nxt=[0]*n; fi=[None]*n
    for _ in range(n*n):
        engaged=set(x for x in fi if x is not None)
        prop={}
        for m in range(n):
            if m not in engaged and nxt[m]<n: prop[m]=manInv[m][nxt[m]]
        newn=[nxt[m]+1 if m in prop else nxt[m] for m in range(n)]
        newf=[]
        for w in range(n):
            c=[m for m in prop if prop[m]==w]+([fi[w]] if fi[w] is not None else [])
            newf.append(min(c,key=lambda m: womanRank[w][m]) if c else None)
        nxt,fi=newn,newf
    mu={}
    for w in range(n):
        if fi[w] is not None: mu[fi[w]]=w
    return mu
def perms(n): return [list(p) for p in itertools.permutations(range(n))]
def randinst(n):
    return [random.sample(range(n),n) for _ in range(n)],[random.sample(range(n),n) for _ in range(n)]
