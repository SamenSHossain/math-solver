# Prove2Me contributions — "Optimal Decision Making Under Strategic Behavior" (Tsirtsis et al., arXiv:1905.09239v5)

Lean 4 proofs for the Prove2Me missions built on this paper (environment: Lean v4.33.1, Mathlib `0df444a`).

## Status of the requested mission

Mission **"Optimal Decision Making Under Strategic Behavior 3: A Three-Value Instance with General Costs
Where No Optimal Policy Is Outcome Monotonic"** has no open frontier: its goal theorem
`StrategicPolicy.NonMonotone.no_outcome_monotonic_optimum` and both milestone theorems
(`optimal_family`, `cost_not_om`) are already PROVED on the platform (the mission page lists an
ACCEPTED submission by SamenHossain on Oct 18, 2026).

## Proofs in this directory (sibling mission, same paper, §3 example)

Two theorems from the same series were still OPEN on the platform and are proved here:

| Platform theorem | Statement (paper numbering) | File |
|---|---|---|
| `StrategicPolicy.StochasticOpt.induced_transport` | Under π* = (1, 0.7, 0): br(3) = 2, br(2) = 1, br(1) = 1 (§3, p. 5) | `Solutions/Sol_StrategicPolicy_StochasticOpt_induced_transport.lean` |
| `StrategicPolicy.StochasticOpt.strategic_beats_nonstrategic` | u_NS(1,γ) < u(π*,γ) and u(1,γ) < u(π*,γ) (§3, p. 5, last sentence) | `Solutions/Sol_StrategicPolicy_StochasticOpt_strategic_beats_nonstrategic.lean` |

The second proof imports the first as a lemma (a tracked reduction on the platform).
`Definitions/` and `Theorems/` are verbatim mirrors of the platform declarations the proofs import
(theorem files end in `by sorry` on purpose, exactly as the platform stores them).
`explanations/` holds the human-readable write-ups attached to each submission.

## Reproducing locally

```bash
# in a workspace pinned to leanprover/lean4:v4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474
lake build Solutions.Sol_StrategicPolicy_StochasticOpt_induced_transport \
           Solutions.Sol_StrategicPolicy_StochasticOpt_strategic_beats_nonstrategic
```
