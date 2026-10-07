**Statement.** Let $P$ be a finite population with $n = |P|$ members, let $\mathit{nbElit} \in \mathbb{N}$ satisfy $\mathit{nbElit} + 1 \le n$, and let $J \in P$ be among the $\mathit{nbElit}$ best individuals of $P$ in terms of fitness, that is,

$$\#\{K \in P : c(K) < c(J)\} < \mathit{nbElit}.$$

Then

$$BF_P(J) \le \frac{\mathit{nbElit}-1}{n-1} + 1 - \frac{\mathit{nbElit}}{n-1} \qquad\text{and}\qquad BF_P(J) < 1,$$

where $BF_P(J) = \mathit{fit}_P(J) + \bigl(1 - \tfrac{\mathit{nbElit}}{n-1}\bigr)\,\mathit{dc}_P(J)$ is the Biased Fitness (7), with $\mathit{fit}_P(J) = \#\{K \in P : c(K) < c(J)\}/(n-1)$ and $\mathit{dc}_P(J) = \#\{K \in P : \Delta_P(J) < \Delta_P(K)\}/(n-1)$.

**Idea.** Both normalized ranks are quotients by $n-1$. The numerator of the fitness rank of an elite individual is at most $\mathit{nbElit}-1$, and the diversity rank is at most $1$ because an individual is never counted as strictly more diverse than itself. Since $\mathit{nbElit} \le n-1$, the coefficient of $\mathit{dc}_P(J)$ is nonnegative, so the two bounds combine into $1 - \frac{1}{n-1}$, which is strictly below $1$. This is the second sentence of the proof of the elitism Proposition in Section 4.6 of the paper, written out with the normalizations made explicit.

**Proof.** *Step 1: the denominator is positive.* The elite hypothesis is a strict inequality between a natural number and $\mathit{nbElit}$, so $\mathit{nbElit} \ge 1$; with $\mathit{nbElit} + 1 \le n$ this gives $n \ge 2$, hence $n - 1 > 0$.

*Step 2: the fitness rank.* The numerator of $\mathit{fit}_P(J)$ is the number of members of $P$ with strictly smaller cost than $J$, which is at most $\mathit{nbElit} - 1$ by hypothesis. Dividing by $n - 1 > 0$,

$$\mathit{fit}_P(J) \le \frac{\mathit{nbElit}-1}{n-1}.$$

*Step 3: the diversity rank.* The set $\{K \in P : \Delta_P(J) < \Delta_P(K)\}$ does not contain $J$, since $\Delta_P(J) < \Delta_P(J)$ is impossible; it is therefore contained in $P \setminus \{J\}$, which has $n - 1$ elements. Consequently

$$0 \le \mathit{dc}_P(J) \le \frac{n-1}{n-1} = 1.$$

*Step 4: the coefficient.* From $\mathit{nbElit} \le n - 1$ we get $\mathit{nbElit}/(n-1) \le 1$, so $1 - \mathit{nbElit}/(n-1) \ge 0$.

*Step 5: conclusion.* Multiplying the upper bound of Step 3 by the nonnegative coefficient of Step 4 and adding the bound of Step 2,

$$BF_P(J) \le \frac{\mathit{nbElit}-1}{n-1} + \Bigl(1 - \frac{\mathit{nbElit}}{n-1}\Bigr) \cdot 1 = \frac{\mathit{nbElit}-1}{n-1} + 1 - \frac{\mathit{nbElit}}{n-1},$$

which is the first claim. Finally $\frac{\mathit{nbElit}-1}{n-1} - \frac{\mathit{nbElit}}{n-1} = -\frac{1}{n-1}$, so the right-hand side equals $1 - \frac{1}{n-1} < 1$ because $\frac{1}{n-1} > 0$. This gives $BF_P(J) < 1$.
