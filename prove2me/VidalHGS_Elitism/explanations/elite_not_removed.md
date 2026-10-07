**Statement.** Consider one subpopulation $P$ with costs $c$, distance $\delta$, diversity contribution $\Delta$, elite parameter $\mathit{nbElit}$, and current best solution $\mathit{best}$, and suppose

$$\mathit{nbElit} + \lambda \le |P|.$$

Let $P'$ be the result of any run of the survivor-selection procedure of Section 4.6 that removes $\lambda$ individuals from $P$ one at a time, each step removing an individual of maximum Biased Fitness in $X$ when $X \neq \emptyset$ and in the whole current population otherwise, with the ranks, the Biased Fitness and $X$ recomputed on the current population before each removal. If $J \in P$, $J \notin X(P)$, and $J$ is among the $\mathit{nbElit}$ best individuals of $P$ in terms of fitness, then

$$J \in P'.$$

This is the Proposition of Section 4.6: using the Biased Fitness function, an individual $I \notin X$ that is part of the $\mathit{nbElit}$ best individuals of the subpopulation in terms of fitness is not removed by the survivor-selection procedure.

**Idea.** The paper proves the Proposition for a single removal and leaves the iteration implicit. The argument here makes the iteration explicit: one removal step never removes $J$ (this is the imported lemma), and the three hypotheses on $J$, together with the size condition, are inherited by the population that remains after the step. Induction on the number of removals then carries $J$ all the way to $P'$.

**The lemma used.** This submission is a reduction: it imports `removalStep_keeps_elite` (third sentence of the paper's proof), which states that if $Q$ arises from $P$ by one removal step, $\mathit{nbElit} + 1 \le |P|$, $J \in P$, $J \notin X(P)$, and $J$ is among the $\mathit{nbElit}$ best individuals of $P$, then $J \in Q$.

**Proof.** We prove, by induction on $k$, that for every population $R_0$ and every run of $k$ removal steps $R_0 \to R_1 \to \cdots \to R_k$: if $\mathit{nbElit} + k \le |R_0|$, $J \in R_0$, $J \notin X(R_0)$, and $J$ is among the $\mathit{nbElit}$ best individuals of $R_0$, then $J \in R_k$. The Proposition is the case $k = \lambda$, $R_0 = P$, $R_k = P'$.

*Base case $k = 0$.* No individual is removed, $R_0 = R_k$, and $J \in R_0$ by hypothesis.

*Inductive step.* Let the first removal take $R_0$ to $Q = R_0 \setminus \{I\}$, followed by a run of $k$ removals from $Q$ to $R_{k+1}$, and assume the hypotheses with $k + 1$ in place of $k$. Since $\mathit{nbElit} + (k+1) \le |R_0|$, in particular $\mathit{nbElit} + 1 \le |R_0|$, and the imported lemma gives $J \in Q$. It remains to check that the induction hypothesis applies to the run from $Q$.

1. *Size.* $|Q| = |R_0| - 1$, so $\mathit{nbElit} + k \le |Q|$.

2. *$J \notin X(Q)$.* Suppose $J \in X(Q)$: then $J \neq \mathit{best}$ and some $K \in Q$, $K \neq J$, satisfies $\delta(K, J) = 0$ or $c(K) = c(J)$. Since $Q \subseteq R_0$, the same $K$ witnesses that $J$ is a clone in $R_0$, so $J \in X(R_0)$, contrary to hypothesis. Thus being outside $X$ is preserved when the population shrinks.

3. *$J$ stays elite.* Since $Q \subseteq R_0$,

$$\#\{K \in Q : c(K) < c(J)\} \le \#\{K \in R_0 : c(K) < c(J)\} < \mathit{nbElit}.$$

By the induction hypothesis applied to the run of $k$ removals from $Q$, $J \in R_{k+1}$, which completes the induction.

**Remarks.** The conclusion holds for every run of the procedure, whatever tie-breaking is used when several individuals attain the maximum Biased Fitness, because the imported lemma only uses the maximality of the removed individual. The hypothesis $\mathit{nbElit} + \lambda \le |P|$ is exactly what keeps the size condition $\mathit{nbElit} + 1 \le |R_i|$ of the one-step lemma valid at every step $i < \lambda$; it corresponds to the paper's setting, where $\mu + \lambda$ individuals are reduced to $\mu$ and $\mathit{nbElit} = el \times \mu \le \mu$ (Table 1).
