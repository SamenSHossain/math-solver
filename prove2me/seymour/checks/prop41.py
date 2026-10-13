"""Brute-force test of Proposition 4.1 of the manuscript: no oriented graph with all indegrees >= 1
satisfies |U| + |F^2(U)| < 2|F(U)| for every nonempty proper U.  Enumerate all oriented graphs on n <= 6
vertices (up to the 3^(n choose 2) orientations), random sample for n = 7, 8."""
import itertools, random, sys
def check(n, adj):  # adj[v] = bitmask of out-neighbours
    full = (1 << n) - 1
    # indegrees positive
    indeg = 0
    for v in range(n): indeg |= adj[v]
    if indeg != full: return False
    F = [0] * (1 << n)
    for U in range(1, 1 << n):
        lsb = U & -U; v = lsb.bit_length() - 1
        F[U] = F[U ^ lsb] | adj[v]
    for U in range(1, full):
        fu = F[U]; f2 = F[fu]
        if not (bin(U).count('1') + bin(f2).count('1') < 2 * bin(fu).count('1')): return False
    return True
def enum(n):
    pairs = list(itertools.combinations(range(n), 2))
    found = 0
    for orient in itertools.product((0, 1, 2), repeat=len(pairs)):
        adj = [0] * n
        for (u, v), o in zip(pairs, orient):
            if o == 1: adj[u] |= 1 << v
            elif o == 2: adj[v] |= 1 << u
        if check(n, adj):
            found += 1; print('FOUND n=%d adj=%s' % (n, adj)); 
            if found > 3: return
    print('n=%d exhaustive: no graph satisfies (17)' % n, flush=True)
def sample(n, trials):
    pairs = list(itertools.combinations(range(n), 2))
    for t in range(trials):
        adj = [0] * n
        for (u, v) in pairs:
            o = random.randrange(3)
            if o == 1: adj[u] |= 1 << v
            elif o == 2: adj[v] |= 1 << u
        if check(n, adj): print('FOUND n=%d adj=%s' % (n, adj)); return
    print('n=%d: %d random samples, none satisfies (17)' % (n, trials), flush=True)
for n in (2, 3, 4, 5): enum(n)
enum(6)
sample(7, 300000); sample(8, 300000); sample(9, 100000)
