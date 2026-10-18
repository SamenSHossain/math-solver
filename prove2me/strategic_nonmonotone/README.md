# Optimal Decision Making Under Strategic Behavior 3 (Prove2Me mission)

Tsirtsis et al., arXiv:1905.09239v5, §5: a three-value instance with general costs where an optimal policy
exists but none is outcome monotonic. **All three theorems of the mission are Proved** (both milestones and the
goal), each with a complete, self-contained proof (no imports of other platform theorems).

- `cost_not_om`: the cost violates outcome monotonicity — moving from x₁ to the lower-outcome x₂ costs 0.2 ≠ 0.
- `optimal_family`: every π with π(x₁) = 1, π(x₂) ≤ 0.7, π(x₃) = 1 is optimal, and x₂ moves to x₁ (the tie at
  π(x₂) = 0.7 is resolved by the outcome tie-break).
- `no_outcome_monotonic_optimum` (goal): an optimum exists and no optimum is outcome monotonic.

**Argument.** The individual at x₃ can never afford to move (costs 1.2 and 1.1 exceed any benefit gain), so its
term is 0.15·π(x₃). Every other term is at most pᵢ·0.9. Hence u ≤ 0.09 + 0.36 + 0.15 = 0.6 on all of [0,1]³, and
the printed family attains 0.6. A maximizer must therefore have π(x₃) = 1 and send x₂ to x₁, which forces
π(x₂) ≤ π(x₁) − 0.3 ≤ 0.7 < π(x₃): the lowest-outcome value gets a strictly larger decision probability than
x₂, contradicting outcome monotonicity.
