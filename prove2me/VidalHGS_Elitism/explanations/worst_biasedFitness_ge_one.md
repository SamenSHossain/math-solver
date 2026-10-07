**Statement.** Let $P$ be a finite population with $n = |P| \ge 2$ members, let $\mathit{nbElit} \in \mathbb{N}$ satisfy $\mathit{nbElit} + 1 \le n$, and suppose the set $X(P)$ of non-best individuals having a clone in $P$ is empty. Let $W \in P$ be an individual of worst fitness, that is, $c(K) \le c(W)$ for every $K \in P$. Then

$$\mathit{fit}_P(W) = 1 \qquad\text{and}\qquad BF_P(W) = \mathit{fit}_P(W) + \Bigl(1 - \frac{\mathit{nbElit}}{n-1}\Bigr)\,\mathit{dc}_P(W) \ge 1,$$

where $\mathit{fit}_P(W) = \#\{K \in P : c(K) < c(W)\}/(n-1)$ and $\mathit{dc}_P(W) = \#\{K \in P : \Delta_P(W) < \Delta_P(K)\}/(n-1)$.

**Idea.** When $X(P)$ is empty, no two individuals of $P$ share a cost: two individuals of equal cost are clones of each other, and at most one of them can be the best solution. Hence every $K \ne W$ in $P$ is strictly better than $W$, the numerator of $\mathit{fit}_P(W)$ is exactly $n - 1$, and the fitness rank is $1$. The remaining term of the Biased Fitness is a product of two nonnegative numbers. This is the first sentence of the proof of the elitism Proposition in Section 4.6 of the paper.

**Proof.** *Step 1: costs in $P$ are pairwise distinct.* Let $K \in P$ with $K \ne W$ and suppose $c(K) = c(W)$. Then $W$ is a clone in $P$, witnessed by $K$, and $K$ is a clone in $P$, witnessed by $W$. Since $X(P) = \emptyset$, no individual of $P$ different from $\mathit{best}$ has a clone in $P$; therefore $W = \mathit{best}$ and $K = \mathit{best}$, contradicting $K \ne W$. Together with the hypothesis $c(K) \le c(W)$ this shows

$$c(K) < c(W) \qquad\text{for every } K \in P,\ K \ne W.$$

*Step 2: the fitness rank.* By Step 1, and since $c(W) < c(W)$ is impossible,

$$\{K \in P : c(K) < c(W)\} = P \setminus \{W\},$$

a set with $n - 1$ elements. Since $n \ge 2$, the denominator $n - 1$ is positive and $\mathit{fit}_P(W) = (n-1)/(n-1) = 1$.

*Step 3: the Biased Fitness.* The diversity rank $\mathit{dc}_P(W)$ is a quotient of a nonnegative integer by $n - 1 > 0$, so $\mathit{dc}_P(W) \ge 0$. From $\mathit{nbElit} \le n - 1$ we get $\mathit{nbElit}/(n-1) \le 1$, so the coefficient $1 - \mathit{nbElit}/(n-1)$ is nonnegative as well. Hence

$$BF_P(W) = 1 + \Bigl(1 - \frac{\mathit{nbElit}}{n-1}\Bigr)\,\mathit{dc}_P(W) \ge 1.$$
