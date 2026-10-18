import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem lemma_3_1 (arrow : X → X → Prop) (R C : Finset (X × X)) :
    ∃ R' ⊆ R, ∃ C' ⊆ C,
      (∀ l ∈ R', ∀ c ∈ C', ¬ Conflict arrow l c) ∧
      (∀ l ∈ R, (∀ c ∈ C, ¬ Conflict arrow l c) → l ∈ R') ∧
      (∀ c ∈ C, (∀ l ∈ R, ¬ Conflict arrow l c) → c ∈ C') ∧
      (R \ R').card + (C \ C').card
        ≤ (pointsH arrow R C).card + (uncovered arrow R C R' C').card := by
  sorry

end OAI.SeymourSecondNeighborhood.Pruning
