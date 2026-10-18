import Mathlib
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_SeymourSecondNeighborhood_Image

open Finset

namespace OAI.SeymourSecondNeighborhood.Pruning

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Matching bound in the augmented bipartite graph `Γ`.** The graph `Γ` has left vertex set
`R ⊔ Z` (members of `R`, and left copies `Sum.inr z` of the points `z ∈ Z = pointsZ arrow R C`)
and right vertex set `C ⊔ Z` (members of `C`, and right copies of the points of `Z`), encoded as
`(X × X) ⊕ (X × X)` on both sides. Its edges are
* the conflict edges `(inl l, inl c)` with `l ∈ R`, `c ∈ C`, `Conflict arrow l c`;
* the left-cover edges `(inl l, inr z)` with `l ∈ R`, `z ∈ Z`, `CoversL arrow l z`;
* the right-cover edges `(inr z, inl c)` with `z ∈ Z`, `c ∈ C`, `CoversR arrow c z`.

Every matching `M` of `Γ` (a set of edges of `Γ` on which both projections are injective) has at
most `|Z| + |H|` edges, where `H = pointsH arrow R C`. -/
theorem matching_bound (arrow : X → X → Prop) (R C : Finset (X × X))
    (M : Finset (((X × X) ⊕ (X × X)) × ((X × X) ⊕ (X × X))))
    (hM : ∀ e ∈ M,
      (∃ l ∈ R, ∃ c ∈ C, e = (Sum.inl l, Sum.inl c) ∧ Conflict arrow l c) ∨
      (∃ l ∈ R, ∃ z ∈ pointsZ arrow R C, e = (Sum.inl l, Sum.inr z) ∧ CoversL arrow l z) ∨
      (∃ z ∈ pointsZ arrow R C, ∃ c ∈ C, e = (Sum.inr z, Sum.inl c) ∧ CoversR arrow c z))
    (h₁ : Set.InjOn Prod.fst (M : Set (((X × X) ⊕ (X × X)) × ((X × X) ⊕ (X × X)))))
    (h₂ : Set.InjOn Prod.snd (M : Set (((X × X) ⊕ (X × X)) × ((X × X) ⊕ (X × X))))) :
    M.card ≤ (pointsZ arrow R C).card + (pointsH arrow R C).card := by
  sorry

end OAI.SeymourSecondNeighborhood.Pruning
