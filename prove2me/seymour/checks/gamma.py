"""Direct test of the matching bound at the heart of Lemma 3.1: in the augmented bipartite graph Gamma,
a maximum matching has size <= |Z| + |H|.  Random instances, |X| up to 6, arbitrary relations (loops allowed)."""
import random, sys, itertools
def max_matching(adj, nl):
    match_r = {}
    def try_aug(u, seen):
        for v in adj[u]:
            if v in seen: continue
            seen.add(v)
            if v not in match_r or try_aug(match_r[v], seen):
                match_r[v] = u; return True
        return False
    return sum(1 for u in range(nl) if try_aug(u, set()))
def instance(n, prel, pfam, maxfam):
    X = range(n)
    rel = {(a, b) for a in X for b in X if random.random() < prel}
    R = [p for p in itertools.product(X, X) if random.random() < pfam][:maxfam]
    C = [p for p in itertools.product(X, X) if random.random() < pfam][:maxfam]
    conf = [(a, b) for a, r in enumerate(R) for b, c in enumerate(C) if (r[0], c[0]) in rel and (c[1], r[1]) in rel]
    Z = sorted({(C[b][0], R[a][1]) for a, b in conf}); H = {(R[a][0], C[b][1]) for a, b in conf}
    zi = {z: k for k, z in enumerate(Z)}
    # left: R (0..|R|-1) then ZL (|R|..); right: C (0..|C|-1) then ZR (|C|..)
    nl = len(R) + len(Z); adj = [[] for _ in range(nl)]
    for a, b in conf: adj[a].append(b)
    for a, r in enumerate(R):
        for z in Z:
            if z[1] == r[1] and (r[0], z[0]) in rel: adj[a].append(len(C) + zi[z])
    for b, c in enumerate(C):
        for z in Z:
            if z[0] == c[0] and (c[1], z[1]) in rel: adj[len(R) + zi[z]].append(b)
    m = max_matching(adj, nl)
    return m, len(Z), len(H), rel, R, C
random.seed(7)
worst = 0; cnt = 0
for n in (2, 3, 4, 5, 6):
    for t in range(40000 if n <= 4 else 15000):
        m, z, h, rel, R, C = instance(n, random.choice((0.3, 0.5, 0.7, 0.9)), random.choice((0.2, 0.4, 0.6, 0.9)), 14)
        cnt += 1
        if m > z + h: print('VIOLATION n=%d |M|=%d |Z|=%d |H|=%d' % (n, m, z, h), rel, R, C); sys.exit()
        worst = max(worst, m - z - h)
print('matching bound ok on %d instances; max(|M| - |Z| - |H|) = %d' % (cnt, worst), flush=True)
