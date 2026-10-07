# VidalHGS.Elitism — Biased-Fitness survivor selection never removes an elite individual

Lean 4 proofs submitted to [Prove2Me](https://prove2.me) for the mission
"A Hybrid Genetic Algorithm for Multidepot and Periodic Vehicle Routing Problems:
Biased-Fitness Survivor Selection Never Removes an Elite Individual Outside X".

Source: Vidal, Crainic, Gendreau, Lahrichi and Rei, *A Hybrid Genetic Algorithm for
Multi-Depot and Periodic Vehicle Routing Problems*, CIRRELT-2010-34 (July 2010),
Section 4.6, Proposition (pp. 16–17).

Environment: Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, Lean `v4.33.1`.

## Layout

The directories mirror the Prove2Me workspace, so the files build unchanged in a
workspace pinned to the environment above (`lake build Solutions.<module>`):

| Path | Content |
|------|---------|
| `Definitions/Def_VidalHGS_Elitism_SurvivorSelection.lean` | Platform definition (verbatim): normalized ranks, Biased Fitness (7), clones, the set `X`, `RemovalStep`, `SurvivorRun`, `IsElite`. |
| `Theorems/Thm_*.lean` | The four platform statements, verbatim, with `by sorry` bodies (local stubs for imports). |
| `Solutions/Sol_*.lean` | The submitted proofs. Each declares a top-level `theorem solution` whose type matches its target exactly. |
| `explanations/*.md` | The human-readable explanations attached to each submission. |

## Proof structure

The decomposition follows the paper's three-sentence proof and the mission's three milestones:

1. `worst_biasedFitness_ge_one` — direct proof. When `X = ∅`, costs are pairwise distinct, so the worst individual `W` has `fit(W) = 1` and `BF(W) ≥ 1`.
2. `elite_biasedFitness_lt_one` — direct proof. An individual among the `nbElit` best has `BF(J) ≤ (nbElit−1)/(n−1) + 1 − nbElit/(n−1) = 1 − 1/(n−1) < 1`.
3. `removalStep_keeps_elite` — reduction importing 1 and 2. One removal step spares `J ∉ X`: if `X = ∅` the removed `I` satisfies `BF(I) ≥ BF(W) ≥ 1 > BF(J)`; if `X ≠ ∅` then `I ∈ X` while `J ∉ X`.
4. `elite_not_removed` (the target) — reduction importing 3. Induction on the run: each step keeps `J`, and the hypotheses (`J ∉ X`, `J` elite, `nbElit + remaining ≤ |P|`) are inherited by the shrunken population.

## Server verdicts (2026-10-07)

| Theorem | Submission | Verdict | Theorem status |
|---------|------------|---------|----------------|
| `VidalHGS.Elitism.worst_biasedFitness_ge_one` | `79420795-9676-4b66-af12-a55ad31dbae4` | ACCEPTED | Proved |
| `VidalHGS.Elitism.elite_biasedFitness_lt_one` | `16076ea0-9f5a-46f7-939e-30051f5c28ee` | ACCEPTED | Proved |
| `VidalHGS.Elitism.removalStep_keeps_elite` | `9863b4c9-e3cd-491f-96ec-f3be6841b683` | ACCEPTED | Proved |
| `VidalHGS.Elitism.elite_not_removed` | `1fe0e4df-f3f1-4f2d-9fad-91035b900358` | ACCEPTED | Proved |

All three mission milestones are marked completed.
