"""Brute-force test of Lemma 3.1 (pruning) on small instances: X of size 2 (exhaustive) and 3 (random).
For each relation -> on X and families R, C subset of X x X, check that some R' subset R, C' subset C with no
conflicts, retaining every initially conflict-free member, satisfies
   |R \ R'| + |C \ C'| <= |H| + #{z in Z : z covered by no member of R' u C'}."""
import itertools, random, sys
def run(X, rel, R, C):
    conf = [(r, c) for r in R for c in C if (r[0], c[0]) in rel and (c[1], r[1]) in rel]
    if not conf: return True
    Z = {(c[0], r[1]) for r, c in conf}; H = {(r[0], c[1]) for r, c in conf}
    freeR = {r for r in R if not any(x == r for x, _ in conf)}
    freeC = {c for c in C if not any(y == c for _, y in conf)}
    def covered(z, Rp, Cp):
        i, j = z
        return any(r[1] == j and (r[0], i) in rel for r in Rp) or any(c[0] == i and (c[1], j) in rel for c in Cp)
    Rl, Cl = list(R), list(C)
    for Rp in (set(s) for k in range(len(Rl), -1, -1) for s in itertools.combinations(Rl, k)):
        if not freeR <= Rp: continue
        for Cp in (set(s) for k in range(len(Cl), -1, -1) for s in itertools.combinations(Cl, k)):
            if not freeC <= Cp: continue
            if any((r[0], c[0]) in rel and (c[1], r[1]) in rel for r in Rp for c in Cp): continue
            q = sum(1 for z in Z if not covered(z, Rp, Cp))
            if len(R) - len(Rp) + len(C) - len(Cp) <= len(H) + q: return True
    return False
def exhaustive2():
    X = [0, 1]; XX = [(a, b) for a in X for b in X]
    cnt = 0
    for relbits in range(16):
        rel = {XX[i] for i in range(4) if relbits >> i & 1}
        for Rb in range(16):
            R = {XX[i] for i in range(4) if Rb >> i & 1}
            for Cb in range(16):
                C = {XX[i] for i in range(4) if Cb >> i & 1}
                cnt += 1
                if not run(X, rel, R, C): print('COUNTEREXAMPLE |X|=2', rel, R, C); return
    print('|X|=2 exhaustive ok (%d cases)' % cnt, flush=True)
def random3(trials, seed=1):
    random.seed(seed)
    X = [0, 1, 2]; XX = [(a, b) for a in X for b in X]
    for t in range(trials):
        rel = {p for p in XX if random.random() < 0.5}
        R = {p for p in XX if random.random() < 0.45}; C = {p for p in XX if random.random() < 0.45}
        if len(R) > 6 or len(C) > 6: continue
        if not run(X, rel, R, C): print('COUNTEREXAMPLE |X|=3', rel, R, C); return
    print('|X|=3 random ok (%d trials)' % trials, flush=True)
exhaustive2(); random3(3000)
