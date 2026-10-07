**Statement.** Let $P$ be a finite population with $n = |P|$ members and $\mathit{nbElit} + 1 \le n$, and let $Q$ be obtained from $P$ by one removal step of the survivor-selection procedure of Section 4.6: with the ranks, the Biased Fitness $BF_P$ and the set $X(P)$ of non-best individuals having a clone all computed on $P$, the removed individual $I \in P$ has maximum $BF_P$ over $X(P)$ if $X(P) \neq \emptyset$, and maximum $BF_P$ over $P$ otherwise, and $Q = P \setminus \{I\}$. If $J \in P$, $J \notin X(P)$, and $J$ is among the $\mathit{nbElit}$ best individuals of $P$ in terms of fitness, then

$$J \in Q.$$

**Idea.** This is the third sentence of the proof of the elitism Proposition ("Individual $J$ will not be removed as $I$ has a worst biased fitness"). It reduces to the two lemmas stated in the first two sentences of that proof: in the branch $X(P) = \emptyset$ the removed individual has a Biased Fitness at least that of the worst individual, which is at least $1$, whereas an elite individual has Biased Fitness strictly below $1$; in the branch $X(P) \neq \emptyset$ the removed individual belongs to $X(P)$, and $J$ does not.

**The two lemmas used.** This submission is a reduction: it imports the following two statements, which are proved separately.

1. `worst_biasedFitness_ge_one` (first sentence of the paper's proof): if $X(P) = \emptyset$, $|P| \ge 2$, $\mathit{nbElit} + 1 \le |P|$, and $W \in P$ has worst fitness, i.e. $c(K) \le c(W)$ for all $K \in P$, then $\mathit{fit}_P(W) = 1$ and $BF_P(W) \ge 1$.

2. `elite_biasedFitness_lt_one` (second sentence of the paper's proof): if $\mathit{nbElit} + 1 \le |P|$ and $J \in P$ is among the $\mathit{nbElit}$ best individuals of $P$, then $BF_P(J) < 1$.

**Proof.** Write $Q = P \setminus \{I\}$ with $I$ the removed individual. Since $J \in P$, it suffices to show $J \neq I$. Suppose, for a contradiction, that $J = I$.

*Case $X(P) = \emptyset$.* In this branch of the procedure, $I$ maximizes $BF_P$ over all of $P$. The elite hypothesis on $J$ forces $\mathit{nbElit} \ge 1$, hence $|P| \ge 2$. As $P$ is nonempty (it contains $J$), it has an individual $W$ of worst fitness, $c(K) \le c(W)$ for all $K \in P$. By Lemma 1, $BF_P(W) \ge 1$; by maximality of $I$, $BF_P(W) \le BF_P(I)$; and by Lemma 2, $BF_P(J) < 1$. With $J = I$ this gives

$$1 \le BF_P(W) \le BF_P(I) = BF_P(J) < 1,$$

a contradiction.

*Case $X(P) \neq \emptyset$.* In this branch the removed individual satisfies $I \in X(P)$. Since $J = I$, this contradicts the hypothesis $J \notin X(P)$. This case is the reason the Proposition assumes $J \notin X$.

In both cases $J \neq I$, so $J \in P \setminus \{I\} = Q$.
