We prove that in the three-value instance of §3 (p. 5), under the policy $\pi^* = (\pi^*(x{=}1), \pi^*(x{=}2), \pi^*(x{=}3)) = (1, 0.7, 0)$, the best responses defined by (5) with tie-break (ii) are

$$\mathrm{br}(3) = 2, \qquad \mathrm{br}(2) = 1, \qquad \mathrm{br}(1) = 1,$$

so the mass $P(x{=}3)$ is transported to $x = 2$ and the mass $P(x{=}2)$ to $x = 1$. In the Lean indexing the feature values $1, 2, 3$ are $0, 1, 2$, so the statement reads $\mathrm{br}(2) = 1$, $\mathrm{br}(1) = 0$, $\mathrm{br}(0) = 0$. The data are $q = (1, 0.7, 0.4)$ and the cost matrix

$$c = \begin{pmatrix} 0 & 0 & 0 \\ 0.3 & 0 & 0 \\ 1.2 & 0.3 & 0 \end{pmatrix},$$

with row $i$ the origin and column $j$ the destination.

**Proof idea.** The best response is defined in two stages: first the set of destinations $k$ maximizing the net benefit $\pi^*(x_k) - c(x_i, x_k)$ (the argmax set of (5)), then, among those, the destinations with the highest outcome probability $q$ (tie-break (ii)), the least index being taken if several remain. Since the feature set has three elements, each stage is a finite comparison of explicit rationals. We compute the argmax set for each origin, then the tie set, and observe that every tie set is a singleton $\{j\}$, whence the best response is $j$ (the minimum of a singleton).

**Step 1: argmax sets.** For an individual at $x = 3$ the net benefits of the destinations $x = 1, 2, 3$ are

$$1 - 1.2 = -0.2, \qquad 0.7 - 0.3 = 0.4, \qquad 0 - 0 = 0,$$

so the argmax set is $\{x{=}2\}$. For an individual at $x = 2$ they are

$$1 - 0.3 = 0.7, \qquad 0.7 - 0 = 0.7, \qquad 0 - 0 = 0,$$

so staying and moving to $x = 1$ tie and the argmax set is $\{x{=}1, x{=}2\}$. For an individual at $x = 1$ they are $1, 0.7, 0$, so the argmax set is $\{x{=}1\}$. In Lean each of these is an extensionality argument over `Fin 3`: after `fin_cases` on the candidate element, the membership condition unfolds to finitely many inequalities between explicit rationals, which `norm_num` decides.

**Step 2: tie-break (ii).** The tie set keeps the maximizers whose outcome probability dominates that of every other maximizer. For $x = 3$ and $x = 1$ the argmax set is already a singleton, so the tie set is the same singleton. For $x = 2$ the two maximizers have outcomes $q(x{=}1) = 1$ and $q(x{=}2) = 0.7$, and since $1 > 0.7$ the tie is broken toward $x = 1$: the tie set is $\{x{=}1\}$. This is exactly the indifference described in the source, where an individual at $x = 2$ is indifferent between staying (benefit $0.7$) and moving to $x = 1$ (benefit $1 - 0.3 = 0.7$), and tie-break (ii) sends them to the higher outcome.

**Step 3: conclusion.** The best response is the minimum of the tie set. Each tie set is a singleton $\{j\}$, and the minimum of a singleton is its element, giving $\mathrm{br}(3) = 2$, $\mathrm{br}(2) = 1$, $\mathrm{br}(1) = 1$ in the paper's numbering. The auxiliary lemma `br_eq_of_tieSet_eq` records this last observation for an arbitrary number of feature values, so it can be reused for any instance in which the tie sets are computed explicitly.
