We prove that in the three-value instance of §3 (p. 5), with $\gamma = 0.1$, $P(x) = (0.1, 0.4, 0.5)$, $P(y{=}1 \mid x) = (1, 0.7, 0.4)$ and the cost matrix of p. 5, the strategic optimum $\pi^* = (1, 0.7, 0)$ beats the non-strategic optimum $\mathbf{1} = (1, 1, 1)$ under both readings of "its counterpart in the non-strategic setting":

$$u_{\mathrm{NS}}(\mathbf{1}, \gamma) < u(\pi^*, \gamma) \qquad\text{and}\qquad u(\mathbf{1}, \gamma) < u(\pi^*, \gamma),$$

where $u$ is the strategic utility (7), regrouped by initial feature value as $u(\pi, \gamma) = \sum_i P(x_i)\,(P(y{=}1 \mid x_{\mathrm{br}(i)}) - \gamma)\,\pi(x_{\mathrm{br}(i)})$, and $u_{\mathrm{NS}}(\pi, \gamma) = \sum_x P(x)\,(P(y{=}1 \mid x) - \gamma)\,\pi(x)$ is the non-strategic utility (2).

**Proof idea.** Both utilities are sums of three explicit terms once the best responses are known. The best responses to $\pi^*$ are supplied by the transport lemma `induced_transport` (this submission imports it as a lemma): $\mathrm{br}(3) = 2$, $\mathrm{br}(2) = 1$, $\mathrm{br}(1) = 1$. The best responses to $\mathbf{1}$ are computed here by the same finite argmax-and-tie-break procedure: under $\mathbf{1}$ every destination yields benefit $1$, so an individual maximizes $1 - c(x_i, x_k)$ by avoiding every positive cost, and nobody moves. The claim then reduces to comparing two rational numbers.

**Step 1: best responses to $\mathbf{1}$.** For an individual at $x = 3$ the net benefits are $1 - 1.2$, $1 - 0.3$, $1 - 0$, so the unique maximizer is $x = 3$. For an individual at $x = 2$ they are $1 - 0.3$, $1$, $1$, so $x = 2$ and $x = 3$ tie; since $q(x{=}2) = 0.7 > 0.4 = q(x{=}3)$, tie-break (ii) keeps the individual at $x = 2$. For an individual at $x = 1$ all three destinations are free and yield $1$; the highest outcome is $q(x{=}1) = 1$, so the individual stays at $x = 1$. Hence $\mathrm{br}_{\mathbf{1}}(i) = i$ for every $i$. In Lean each argmax set and tie set is computed by extensionality over `Fin 3` followed by `norm_num`, and the best response is read off as the minimum of a singleton tie set.

**Step 2: the utilities.** With everybody staying, the strategic utility of $\mathbf{1}$ coincides with its non-strategic utility:

$$u(\mathbf{1}, 0.1) = u_{\mathrm{NS}}(\mathbf{1}, 0.1) = 0.1\,(1 - 0.1) + 0.4\,(0.7 - 0.1) + 0.5\,(0.4 - 0.1) = 0.09 + 0.24 + 0.15 = 0.48.$$

For $\pi^*$, the individuals at $x = 1$ and $x = 2$ end up at $x = 1$ (outcome $1$, decision probability $1$) and the individuals at $x = 3$ end up at $x = 2$ (outcome $0.7$, decision probability $0.7$):

$$u(\pi^*, 0.1) = 0.1\,(1 - 0.1)\cdot 1 + 0.4\,(1 - 0.1)\cdot 1 + 0.5\,(0.7 - 0.1)\cdot 0.7 = 0.09 + 0.36 + 0.21 = 0.66.$$

**Step 3: conclusion.** Since $0.48 < 0.66$, both inequalities hold. In Lean, after rewriting the six best-response values, `Fin.sum_univ_three` expands each utility into its three terms, the instance's constants are unfolded, and `norm_num` verifies the resulting rational inequalities.
