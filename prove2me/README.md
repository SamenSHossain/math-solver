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

Both were submitted on 2026-10-31 and verified server-side:

| Theorem | Submission id | Verdict |
|---|---|---|
| `induced_transport` | `16e195c2-adb7-4b63-9c28-4e17e0fcec46` | ACCEPTED |
| `strategic_beats_nonstrategic` | `fd96616e-ecdd-4249-ade3-523f0231aa7b` | ACCEPTED |

These were milestones 3 and 4 of mission "Optimal Decision Making Under Strategic Behavior 2: A Three-Value
Instance with Outcome Monotonic Costs Whose Optimal Policies Are All Stochastic" (mission id
`14325a0c-1498-4c00-b8b9-792b7a4e5f1d`); with them, all four of that mission's milestones are complete.
`Definitions/` and `Theorems/` are verbatim mirrors of the platform declarations the proofs import
(theorem files end in `by sorry` on purpose, exactly as the platform stores them).
`explanations/` holds the human-readable write-ups attached to each submission.

## Reproducing locally

```bash
# in a workspace pinned to leanprover/lean4:v4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474
lake build Solutions.Sol_StrategicPolicy_StochasticOpt_induced_transport \
           Solutions.Sol_StrategicPolicy_StochasticOpt_strategic_beats_nonstrategic
```

## Symmetric rendezvous on the line — sketch for `SymmetricRendezvousLine.symmetric_rendezvous_value_eq_seventeen_quarters`

Mission "Symmetric Rendezvous on the Line" (id `919ee309-fbf8-4cd1-98b5-3da985dd77fa`). The goal is the
Han–Du–Vera–Zuluaga conjecture $R = 17/4$ (Open Problem Garden), a genuine open problem with proved window
$4.1520 < R < 4.2574$; the Lean definitions are a faithful model (ENNReal values, Lebesgue integrals over a
product probability space, infimum over all mixed strategies), so no direct proof or disproof is accessible.
The contribution is a **proof-sketch** that decomposes the goal along the HDVZ structure (submitted 2026-10-31):

| Theorem | Role | Status | Submission |
|---|---|---|---|
| `symmetric_rendezvous_value_le_discrete` (new) | $R \le R_{\mathrm{disc}}$, trivial half of the HDVZ reduction | Proved | `4f818085-2cfb-4514-8c6b-d69aada5879e` ACCEPTED |
| `symmetric_rendezvous_value_eq_discrete` (milestone) | $R = R_{\mathrm{disc}}$, HDVZ dominance theorem | Open | — |
| `discrete_symmetric_rendezvous_value_le_seventeen_quarters` (new) | upper half of the conjecture in the discrete model | Open | — |
| `discrete_symmetric_rendezvous_value_ge_seventeen_quarters` (new) | lower half of the conjecture in the discrete model | Open | — |
| `symmetric_rendezvous_value_eq_seventeen_quarters` (goal) | $R \le R_{\mathrm{disc}} \le 17/4$ and $17/4 \le R_{\mathrm{disc}} = R$ | Open (sketched) | `74f9e4fe-62a5-4c82-90f0-e5a1e85dac45` SKETCH_ACCEPTED |

Files: `Solutions/Sol_SymmetricRendezvousLine_symmetric_rendezvous_value_le_discrete.lean` (direct proof) and
`Solutions/Sol_SymmetricRendezvousLine_symmetric_rendezvous_value_eq_seventeen_quarters.lean` (the sketch);
`Theorems/Thm_SymmetricRendezvousLine_*.lean` are the platform statements (with `sorry`) the sketch imports.
