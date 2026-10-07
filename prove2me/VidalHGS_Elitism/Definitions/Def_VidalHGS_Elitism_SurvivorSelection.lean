import Mathlib

namespace VidalHGS.Elitism

variable {α : Type*} [DecidableEq α]

/-- Normalized fitness rank `fit(I)` (Section 4.3, p. 12): the number of individuals of the
current population `P` with strictly smaller (better) cost `c`, divided by `nbIndiv − 1`, where
`nbIndiv = |P|`. The best individual has rank `0`; with pairwise distinct costs the worst has
rank `1`. Ties share the better rank. The division is in `ℝ`. -/
noncomputable def fitRank (c : α → ℝ) (P : Finset α) (I : α) : ℝ :=
  ((P.filter (fun J => c J < c I)).card : ℝ) / ((P.card : ℝ) - 1)

/-- Normalized diversity-contribution rank `dc(I)` (Section 4.3, p. 12): the number of
individuals of the current population `P` whose diversity contribution `Δ P J` is strictly
larger (better) than `Δ P I`, divided by `nbIndiv − 1`. The diversity contribution `Δ P`
is recomputed on the current population. -/
noncomputable def dcRank (Δ : Finset α → α → ℝ) (P : Finset α) (I : α) : ℝ :=
  ((P.filter (fun J => Δ P I < Δ P J)).card : ℝ) / ((P.card : ℝ) - 1)

/-- Biased Fitness (7), p. 12:
`BF(I) = fit(I) + (1 − nbElit / (nbIndiv − 1)) × dc(I)`, with `nbIndiv = |P|`. -/
noncomputable def biasedFitness (c : α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ)
    (P : Finset α) (I : α) : ℝ :=
  fitRank c P I + (1 - (nbElit : ℝ) / ((P.card : ℝ) - 1)) * dcRank Δ P I

/-- `I` is a clone in `P` (Section 4.6, p. 16): some other individual `J ∈ P`, `J ≠ I`, has the
same attributes as `I` (`δ J I = 0`) or the same fitness (`c J = c I`). -/
def IsClone (c : α → ℝ) (δ : α → α → ℝ) (P : Finset α) (I : α) : Prop :=
  ∃ J ∈ P, J ≠ I ∧ (δ J I = 0 ∨ c J = c I)

open Classical in
/-- The set `X` (Section 4.6, p. 16): the individuals of `P`, different from the current best
solution `best`, that have a clone in `P`. -/
noncomputable def cloneSet (c : α → ℝ) (δ : α → α → ℝ) (best : α) (P : Finset α) :
    Finset α :=
  P.filter (fun I => I ≠ best ∧ IsClone c δ P I)

/-- One removal of the survivor-selection procedure (Section 4.6, p. 16): `Q = P \ {I}` where,
with `X`, the ranks and the Biased Fitness all computed on the current population `P`,
* if `X ≠ ∅`, `I ∈ X` has maximum Biased Fitness over `X`;
* otherwise, `I ∈ P` has maximum Biased Fitness over `P`.
Ties in the maximum are broken arbitrarily. -/
def RemovalStep (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ) (best : α)
    (P Q : Finset α) : Prop :=
  ∃ I ∈ P, Q = P.erase I ∧
    ((cloneSet c δ best P).Nonempty →
      I ∈ cloneSet c δ best P ∧
        ∀ K ∈ cloneSet c δ best P, biasedFitness c Δ nbElit P K ≤ biasedFitness c Δ nbElit P I) ∧
    (cloneSet c δ best P = ∅ →
      ∀ K ∈ P, biasedFitness c Δ nbElit P K ≤ biasedFitness c Δ nbElit P I)

/-- `SurvivorRun … n P R`: the survivor-selection procedure removes `n` individuals from `P`,
one `RemovalStep` at a time ("Update the distance measures and X, and repeat"), ending at `R`. -/
inductive SurvivorRun (c : α → ℝ) (δ : α → α → ℝ) (Δ : Finset α → α → ℝ) (nbElit : ℕ)
    (best : α) : ℕ → Finset α → Finset α → Prop
  | zero (P : Finset α) : SurvivorRun c δ Δ nbElit best 0 P P
  | succ {n : ℕ} {P Q R : Finset α} :
      RemovalStep c δ Δ nbElit best P Q → SurvivorRun c δ Δ nbElit best n Q R →
        SurvivorRun c δ Δ nbElit best (n + 1) P R

/-- `J` is among the `nbElit` best individuals of `P` in terms of fitness: fewer than `nbElit`
members of `P` have strictly smaller cost. -/
def IsElite (c : α → ℝ) (nbElit : ℕ) (P : Finset α) (J : α) : Prop :=
  (P.filter (fun K => c K < c J)).card < nbElit

end VidalHGS.Elitism
