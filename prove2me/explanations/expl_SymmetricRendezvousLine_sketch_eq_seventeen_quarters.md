This submission is a **reduction** of the Han–Du–Vera–Zuluaga conjecture

$$R=\frac{17}{4}$$

(the symmetric rendezvous value on the line, with players starting at distance $2$, independent random orientations, speed at most $1$, and a common mixed strategy) to three statements in the discrete model, following the structure of the literature: every known bound on $R$ is proved in the model where players move at full speed and change direction only at integer times, and Han, Du, Vera and Zuluaga showed that this discrete model loses nothing. The children of this sketch are assumptions here, not results.

**Children.**

1. `symmetric_rendezvous_value_le_discrete`: $R\le R_{\mathrm{disc}}$, where $R_{\mathrm{disc}}$ is the infimum of $E(S,S)$ over mixed strategies supported on integer zigzags. This is the trivial half of the HDVZ reduction (an infimum over a larger family is smaller) and is proved directly.

2. `symmetric_rendezvous_value_eq_discrete` (mission milestone, HDVZ reduction): $R=R_{\mathrm{disc}}$. Its content is the dominance theorem: integer-time full-speed strategies dominate among all strategies.

3. `discrete_symmetric_rendezvous_value_le_seventeen_quarters` (upper half of the conjecture, discrete model): $R_{\mathrm{disc}}\le 17/4$, i.e. for every $\varepsilon>0$ some single mixed strategy over integer zigzags, used by both players, has expected meeting time at most $17/4+\varepsilon$. This is the "explicit strategies" side of the problem; the best proved bound of this kind is $R<4.2574$.

4. `discrete_symmetric_rendezvous_value_ge_seventeen_quarters` (lower half of the conjecture, discrete model): $17/4\le R_{\mathrm{disc}}$, i.e. every mixed strategy over integer zigzags, used by both players, has expected meeting time at least $17/4$. This is the "certificate over all strategies" side; the best proved bound of this kind is $4.1520<R$.

**Why the reduction is valid.** Equality in $[0,\infty]$ follows from the two inequalities.

*Upper half.* Chaining child 1 with child 3,

$$R\le R_{\mathrm{disc}}\le\frac{17}{4}.$$

Note that this direction does not use the dominance theorem: an explicit family of discrete strategies approaching $17/4$ bounds $R$ directly.

*Lower half.* By child 2, $R=R_{\mathrm{disc}}$, so child 4 gives

$$\frac{17}{4}\le R_{\mathrm{disc}}=R.$$

Here the dominance theorem is essential: a lower-bound certificate over integer-zigzag strategies says nothing about arbitrary strategies without it.

Combining the two halves, $R=17/4$. In Lean the proof is `le_antisymm` of the two chains above, the second after rewriting $R$ to $R_{\mathrm{disc}}$ with child 2.

**What remains open.** Children 3 and 4 are the two halves of the conjecture itself, now stated in the discrete model where all numerical work on this problem takes place; child 2 is the mission's reduction milestone. Proving child 2 together with the two halves resolves the goal.
